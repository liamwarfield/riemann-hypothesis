module

public import ReciprocityTheory.GroupCohomology.InfRes

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.CupCorB
section -- merged from ReciprocityTheory.GroupCohomology.CupCorA
namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem mkR_eq {a b : G} :
    Quotient.mk (QuotientGroup.rightRel U) a = Quotient.mk _ b ↔ b * a⁻¹ ∈ U :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

theorem rep_mul (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by
  unfold rep
  congr 1
  rw [mkR_eq]
  simpa [mul_inv_rev] using U.inv_mem x.2

theorem retr_mul (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by
  apply Subtype.ext
  simp only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]

theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

theorem continuous_rep (hU : IsOpen (U : Set G)) : Continuous (rep U) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hmem : (fun y => y * g⁻¹) ⁻¹' (U : Set G) ∈ nhds g := by
    apply (hU.preimage (continuous_mul_const g⁻¹)).mem_nhds
    simp [U.one_mem]
  apply (continuousAt_const (y := rep U g)).congr
  filter_upwards [hmem] with y hy
  have h1 : rep U ((⟨y * g⁻¹, hy⟩ : U) * g) = rep U g := rep_mul U ⟨y * g⁻¹, hy⟩ g
  simpa using h1.symm

theorem continuous_retr (hU : IsOpen (U : Set G)) : Continuous (retr U) :=
  Continuous.subtype_mk (continuous_id.mul (continuous_rep U hU).inv) _

instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm

def cosetMul (g : G) (c : Quotient (QuotientGroup.rightRel U)) : Quotient (QuotientGroup.rightRel U) :=
  Quotient.mk _ (c.out * g)

theorem cosetMul_bij (g : G) : Bijective (cosetMul U g) := by
  have key : ∀ h : G, ∀ c, cosetMul U h⁻¹ (cosetMul U h c) = c := by
    intro h c
    unfold cosetMul
    conv_rhs => rw [← Quotient.out_eq c]
    rw [mkR_eq]
    have hw : (c.out * h) * (Quotient.mk (QuotientGroup.rightRel U) (c.out * h)).out⁻¹ ∈ U :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out (c.out * h))
    simpa [mul_inv_rev, mul_assoc] using hw
  exact ⟨Function.LeftInverse.injective (key g), Function.RightInverse.surjective (fun c => by
    simpa using key g⁻¹ c)⟩

theorem out_mul (g : G) (c : Quotient (QuotientGroup.rightRel U)) :
    c.out * g = (retr U (c.out * g) : G) * (cosetMul U g c).out := by
  rw [retr_spec]
  simp [rep, cosetMul]

end Retr

section Norm

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]

def normF (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i)

theorem normF_eq [Fintype (Quotient (QuotientGroup.rightRel U))] (n : ℕ) (F : (Fin (n + 1) → G) → M.V)
    (x : Fin (n + 1) → G) :
    normF M U n F x = ∑ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i) :=
  finsum_eq_sum_of_fintype _

theorem continuous_rho (s : G) : Continuous (M.rho s) :=
  M.cont.comp (continuous_const.prodMk continuous_id)

theorem normF_mem (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (hF : F ∈ hcoch (M.resSub U) G n) :
    normF M U n F ∈ hcoch M G n := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  refine ⟨?_, fun g x => ?_⟩
  · have : normF M U n F = fun x => ∑ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * x i) := funext (normF_eq M U n F)
    rw [this]
    refine continuous_finsetSum _ fun c _ => (continuous_rho M _).comp (hF.1.comp ?_)
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [normF_eq, normF_eq, map_sum]
      have key : ∀ c : Quotient (QuotientGroup.rightRel U),
          M.rho c.out⁻¹ (F fun i => c.out * (g • x i)) =
          M.rho g (M.rho (cosetMul U g c).out⁻¹ (F fun i => (cosetMul U g c).out * x i)) := by
        intro c
        have e := out_mul U g c
        have h1 : (fun i => c.out * (g • x i)) =
            fun i => retr U (c.out * g) • ((cosetMul U g c).out * x i) := by
          funext i
          show c.out * (g * x i) = (retr U (c.out * g) : G) * ((cosetMul U g c).out * x i)
          rw [← mul_assoc, ← mul_assoc, ← e]
        rw [h1, hF.2]
        show M.rho c.out⁻¹ (M.rho (retr U (c.out * g) : G) _) = _
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        rw [show (retr U (c.out * g) : G) = c.out * g * ((cosetMul U g c).out)⁻¹ by
          rw [eq_mul_inv_iff_mul_eq]; exact e.symm]
        group
      simp only [key]
      exact Fintype.sum_bijective _ (cosetMul_bij U g) _ _ fun _ => rfl

theorem normF_hd (n : ℕ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U (n + 1) (hd n F) = hd n (normF M U n F) := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [normF_eq, hd, map_sum, map_zsmul, Finset.smul_sum]
  exact Finset.sum_comm

variable {M U}

end Norm

end

end ReciprocityTheory.Coh.CCA
end

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Leibniz

variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

def hcup (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V) (F' : (Fin (q + 1) → X) → W)
    (x : Fin (p + q + 1) → X) : Z :=
  β (F fun i => x ⟨i, by omega⟩) (F' fun j => x ⟨p + j, by omega⟩)

theorem val_succAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i.succAbove k : ℕ) = if (k : ℕ) < i then (k : ℕ) else k + 1 := by
  by_cases h : (k : ℕ) < i
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr h), Fin.coe_castSucc]
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (Nat.le_of_not_lt h)),
      Fin.val_succ]

theorem x_congr {n : ℕ} (x : Fin n → X) (a b : Fin n) (h : (a : ℕ) = b) : x a = x b := congrArg x (Fin.ext h)

theorem hd_hcup (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F' : (Fin (q + 1) → X) → W) (hF : hd p F = 0) :
    hd (p + q) (hcup β p q F F') = (-1 : ℤ) ^ p • hcup β p (q + 1) F (hd q F') := by
  funext x
  have hF' := congrFun hF (fun k : Fin (p + 2) => x ⟨k, by omega⟩)
  simp only [hd, Pi.zero_apply] at hF'
  rw [Fin.sum_univ_castSucc] at hF'
  have e0 : F (fun j => x ⟨((Fin.last (p + 1)).succAbove j : ℕ), by omega⟩) =
      F (fun i => x ⟨i, by omega⟩) := by
    congr 1; funext k; congr 1; ext; simp [val_succAbove]
  rw [e0] at hF'
  have hsum : ∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      F (fun j => x ⟨((Fin.castSucc a).succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • F (fun i => x ⟨i, by omega⟩) := by
    have h2 := eq_neg_of_add_eq_zero_left hF'
    simp only [Fin.val_castSucc, Fin.val_last] at h2
    rw [h2, pow_succ, mul_neg_one, neg_smul, neg_neg]
  have h : p + 1 + (q + 1) = p + q + 2 := by omega
  have key : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) +
      ∑ b : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + b : ℕ) • β (F fun i => x ⟨i, by omega⟩)
        (F' fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • β (F fun i => x ⟨i, by omega⟩)
        ((-1 : ℤ) ^ ((0 : Fin (q + 2)) : ℕ) • F' (fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) +
          ∑ b : Fin (q + 1), (-1 : ℤ) ^ (b.succ : ℕ) • F' (fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩)) := by
    have s1 : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
        β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) =
        β (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩)
          (F' fun j => x ⟨p + 1 + j, by omega⟩) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply]
    have e1 : (F' fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) =
        F' fun j => x ⟨p + 1 + j, by omega⟩ := by
      congr 1; funext k; congr 1; ext; simp [val_succAbove]; omega
    rw [s1, hsum, e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Fin.val_zero, pow_zero, one_smul, map_add (f := _), map_sum, map_zsmul, smul_add, Finset.smul_sum,
      smul_smul, Fin.val_succ, LinearMap.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← pow_add]; congr 2; omega
  rw [Pi.smul_apply]
  unfold hd hcup
  beta_reduce
  conv_lhs => rw [← (finCongr h).sum_comp, Fin.sum_univ_add]
  conv_rhs => rw [Fin.sum_univ_succ]
  convert key using 4
  all_goals first
    | (simp; done)
    | (congr 2 <;> (try funext k) <;> (try congr 1) <;> (try funext k) <;> (first | apply x_congr | apply Fin.ext) <;>
        simp only [val_succAbove, finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] <;> (try split_ifs) <;>
        (try simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] at *) <;> omega)

end Leibniz

section PartialProd

theorem pp_trunc {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) (k : Fin (p + 1)) :
    Fin.partialProd (fun i : Fin p => g (Fin.castAdd q i)) k = Fin.partialProd g ⟨k, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp k.isLt)]
  rfl

theorem prod_castAdd {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) :
    (List.ofFn fun i : Fin p => g (Fin.castAdd q i)).prod = Fin.partialProd g ⟨p, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rfl

theorem pp_tail {K : Type*} [Group K] {p q : ℕ} (g : Fin (p + q) → K) (j : Fin q) :
    (Fin.partialProd g ⟨p + j, by omega⟩)⁻¹ * Fin.partialProd g ⟨p + j + 1, by omega⟩ =
      g (Fin.natAdd p j) := by
  rw [show (⟨p + j + 1, by omega⟩ : Fin (p + q + 1)) = Fin.succ (⟨p + j, by omega⟩ : Fin (p + q)) from
    Fin.ext rfl, Fin.partialProd_succ]
  exact inv_mul_cancel_left _ _

theorem pp_of_one {K : Type*} [Group K] {n : ℕ} (t : Fin (n + 1) → K) (h0 : t 0 = 1) (k : Fin (n + 1)) :
    Fin.partialProd (fun i : Fin n => (t i.castSucc)⁻¹ * t i.succ) k = t k := by
  induction k using Fin.induction with
  | zero => rw [Fin.partialProd_zero, h0]
  | succ i ih => rw [Fin.partialProd_succ, ih, mul_inv_cancel_left]

end PartialProd

section Homz

variable {R : Type u} [CommRing R]

def homz {K V : Type u} [Group K] [AddCommGroup V] [Module R V] (ρ : Representation R K V) (n : ℕ)
    (f : (Fin n → K) → V) (x : Fin (n + 1) → K) : V :=
  ρ (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]

theorem resSub_rho_one (M : TRep R G) (v : M.V) : (M.resSub U).rho 1 v = v := by
  simp
  rfl

theorem cor_cup_eq (b : Pairing M N P) (bU : Pairing (M.resSub U) (N.resSub U) (P.resSub U))
    (hb : bU.β = b.β) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V) (g : Fin (p + q) → G) :
    corFun P U (p + q) (cupFun bU p q f (fun h => f' fun i => (h i : G))) g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (fun x => homz N.rho q f' (fun i => (retr U (x i) : G)))) (Fin.partialProd g) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  have hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1 := by
    intro c
    apply Subtype.ext
    show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1
    rw [Quotient.out_eq, mul_inv_cancel]
  have h0 : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  unfold cupFun corFun normF
  simp only [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero, hb]
  have hprod : (List.ofFn fun i : Fin p =>
      (retr U (c.out * Fin.partialProd g (Fin.castAdd q i).castSucc))⁻¹ *
        retr U (c.out * Fin.partialProd g (Fin.castAdd q i).succ)).prod =
      retr U (c.out * Fin.partialProd g ⟨p, by omega⟩) := by
    have h1 := pp_of_one (fun k : Fin (p + 1) => retr U (c.out * Fin.partialProd g ⟨k, by omega⟩))
      (by show retr U (c.out * Fin.partialProd g ⟨0, by omega⟩) = 1; rw [h0, mul_one, hr1])
      (Fin.last p)
    refine Eq.trans ?_ h1
    simp only [Fin.partialProd, Fin.val_last]
    rw [List.take_of_length_le (by simp)]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hprod, h0, mul_one, hr1]
  erw [resSub_rho_one]
  rfl

theorem cup_cor_eq (b : Pairing M N P) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V)
    (g : Fin (p + q) → G) :
    cupFun b p q (corFun M U p f) f' g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (homz N.rho q f')) (Fin.partialProd g) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  have hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1 := by
    intro c
    apply Subtype.ext
    show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1
    rw [Quotient.out_eq, mul_inv_cancel]
  have htail : ∀ j : Fin q, (Fin.partialProd g ⟨p + ↑j, by omega⟩)⁻¹ *
      Fin.partialProd g ⟨p + (↑j + 1), by omega⟩ = g (Fin.natAdd p j) := fun j => pp_tail g j
  have h0 : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  unfold cupFun corFun normF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero]
  simp only [pp_trunc, Fin.coe_castSucc, Fin.val_succ]
  rw [h0, mul_one, hr1]
  erw [resSub_rho_one]
  rw [prod_castAdd]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, htail]
  rw [← b.equiv]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]

end Homz

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem hcup_mem {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {X : Type u}
    [TopologicalSpace X] [MulAction K X] {M N P : TRep R K} (b : Pairing M N P) (p q : ℕ)
    (F : (Fin (p + 1) → X) → M.V) (F' : (Fin (q + 1) → X) → N.V) (hF : F ∈ hcoch M X p)
    (hF' : F' ∈ hcoch N X q) : hcup b.β p q F F' ∈ hcoch P X (p + q) := by
  simp only [hcoch] at hF hF' ⊢
  refine ⟨?_, fun g x => ?_⟩
  · have h1 : Continuous (fun x : Fin (p + q + 1) → X => F fun i : Fin (p + 1) => x ⟨i, by omega⟩) :=
      hF.1.comp (continuous_pi fun i => continuous_apply _)
    have h2 : Continuous
        (fun x : Fin (p + q + 1) → X => F' fun j : Fin (q + 1) => x ⟨p + j, by omega⟩) :=
      hF'.1.comp (continuous_pi fun j => continuous_apply _)
    exact b.cont.comp (h1.prodMk h2)
  · simp only [hcup]
    rw [hF.2 g (fun i => x ⟨i, by omega⟩), hF'.2 g (fun j => x ⟨p + j, by omega⟩), b.equiv]

theorem hcup_sub_right {X V W Z : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F₁ F₂ : (Fin (q + 1) → X) → W) :
    hcup β p q F (F₁ - F₂) = hcup β p q F F₁ - hcup β p q F F₂ := by
  funext x
  simp only [hcup, Pi.sub_apply, map_sub]

theorem hd_zsmul {V X : Type u} [AddCommGroup V] (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → X) → V) :
    hd n (c • F) = c • hd n F := by
  funext x
  unfold hd
  simp only [Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem retr_pull_mem (hU : IsOpen (U : Set G)) {M : TRep R G} (n : ℕ) (F : (Fin (n + 1) → U) → M.V)
    (hF : F ∈ hcoch (M.resSub U) U n) :
    (fun x : Fin (n + 1) → G => F fun i => retr U (x i)) ∈ hcoch (M.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  unfold retr rep
  have hcont : Continuous (fun y : G => (⟦y⟧ : Quotient (QuotientGroup.rightRel U)).out) := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => y * x⁻¹) ⁻¹' (U : Set G), hU.preimage (continuous_mul_const _), by simp,
      fun y hy => ?_⟩
    congr 1
    exact (Quotient.sound (QuotientGroup.rightRel_apply.mpr hy)).symm
  refine ⟨?_, fun g x => ?_⟩
  · refine hF.1.comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).mul ((hcont.comp (continuous_apply i)).inv)).subtype_mk _
  · have hq : ∀ i, (⟦(g : G) * x i⟧ : Quotient (QuotientGroup.rightRel U)) = ⟦x i⟧ := fun i =>
      Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
    dsimp only
    rw [← hF.2]
    congr 1
    funext i
    apply Subtype.ext
    simp [hq i, Subgroup.smul_def, smul_eq_mul, mul_assoc]

theorem res_mem {N : TRep R G} (n : ℕ) (F : (Fin (n + 1) → G) → N.V) (hF : F ∈ hcoch N G n) :
    F ∈ hcoch (N.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  exact ⟨hF.1, fun g x => hF.2 g x⟩

theorem homog_eq {P : TRep R G} (e : ∀ n, P.coch.X n ≃ₗ[R] hcoch P G n)
    (h1 : ∀ n f x, (e n f).1 x = P.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) (n : ℕ)
    (f : P.coch.X n) (F : (Fin (n + 1) → G) → P.V) (hF : F ∈ hcoch P G n)
    (hf : ∀ g, f.1 g = F (Fin.partialProd g)) : (e n f).1 = F := by
  funext x
  rw [h1, hf]
  have ht : (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun i : Fin n => ((x 0)⁻¹ * x i.castSucc)⁻¹ * ((x 0)⁻¹ * x i.succ) := by
    funext i
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hp : Fin.partialProd (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun k => (x 0)⁻¹ * x k := by
    funext k
    rw [ht]
    exact pp_of_one (fun k => (x 0)⁻¹ * x k) (inv_mul_cancel _) k
  rw [hp]
  simp only [hcoch] at hF
  have h2 := hF.2 (x 0) (fun k => (x 0)⁻¹ * x k)
  simp only [smul_eq_mul, mul_inv_cancel_left] at h2
  exact h2.symm

variable [U.FiniteIndex]

theorem normF_sub {M : TRep R G} (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F - F') = normF M U n F - normF M U n F' := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  funext x
  simp only [normF, Pi.sub_apply, map_sub, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib]

theorem normF_zsmul {M : TRep R G} (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U n (c • F) = c • normF M U n F := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  funext x
  simp only [normF, Pi.smul_apply, map_zsmul, finsum_eq_sum_of_fintype, Finset.smul_sum]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.Coh.CCA
end

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u


set_option maxHeartbeats 800000 in
theorem cupCor_holds : CupCorStatement.{u} := by
  unfold CupCorStatement
  intro R _ G _ _ _ M N P U _ b bU cup cupU corM corP hU hβ hcup hcupU hcorM hcorP p q x y
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have ha' : (M.resSub U).coch.d p a = 0 := LinearMap.mem_ker.mp ha
  have hc' : N.coch.d q c = 0 := LinearMap.mem_ker.mp hc
  obtain ⟨eM, hMh, hM1, -⟩ := homogIso_holds.{u} R U (M.resSub U)
  obtain ⟨eN, hNh, hN1, -⟩ := homogIso_holds.{u} R G N
  obtain ⟨eP, hPh, hP1, -⟩ := homogIso_holds.{u} R G P

  have hAM : (eM p a).1 = CCA.homz (M.resSub U).rho p a.1 := funext fun z => hM1 p a z
  have hAmemU : CCA.homz (M.resSub U).rho p a.1 ∈ hcoch (M.resSub U) U p := by
    rw [← hAM]; exact (eM p a).2
  have hA : (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      ∈ hcoch (M.resSub U) G p :=
    CCA.retr_pull_mem (U := U) (hU := hU) (n := p) (F := CCA.homz (M.resSub U).rho p a.1)
      (hF := hAmemU)
  have hA0 : hd p (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) = 0 := by
    have h := hMh p a
    rw [ha', map_zero] at h
    funext z
    have h2 := congrFun h (fun i => retr U (z i))
    rw [← hAM]
    exact h2.symm

  have hFcE : (eN q c).1 = CCA.homz N.rho q c.1 := funext fun z => hN1 q c z
  have hFcN : CCA.homz N.rho q c.1 ∈ hcoch N G q := by
    rw [← hFcE]; exact (eN q c).2
  have hFc0 : hd q (CCA.homz N.rho q c.1) = 0 := by
    have h := hNh q c
    rw [hc', map_zero] at h
    rw [← hFcE]
    exact h.symm
  obtain ⟨FcA, hFcA⟩ : ∃ F : (HomogeneousCochainIso.hcx (N.resSub U) G).X q, F.1 = CCA.homz N.rho q c.1 :=
    ⟨⟨CCA.homz N.rho q c.1, CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN)⟩,
      rfl⟩

  have hcont : Continuous (fun g : G => ((retr U g : U) : G)) :=
    continuous_subtype_val.comp (CCA.continuous_retr (U := U) hU)
  have hequiv : ∀ (v : U) (g : G), ((retr U (v • g) : U) : G) = v • ((retr U g : U) : G) := by
    intro v g
    show ((retr U ((v : G) * g) : U) : G) = (v : G) * ((retr U g : U) : G)
    rw [CCA.retr_mul, Subgroup.coe_mul]
  have hpr := prism_holds.{u} R U (N.resSub U) G G (HomogeneousCochainIso.hcx (N.resSub U) G)
    (HomogeneousCochainIso.hcx (N.resSub U) G) (fun n => LinearEquiv.refl R _) (fun n => LinearEquiv.refl R _)
    (fun n F => rfl) (fun n F => rfl)
  obtain ⟨φ, hφ⟩ := hpr.1 (fun g => ((retr U g : U) : G)) hcont hequiv
  have huq := hpr.2 (fun g => ((retr U g : U) : G)) id φ (Cx.Hom.id _) hcont continuous_id hequiv
    (fun _ _ => rfl) hφ (fun _ _ _ => rfl) q
  have h0 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q FcA = 0 := by
    apply Subtype.ext
    show hd q FcA.1 = 0
    rw [hFcA]; exact hFc0
  have h1 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q (φ.f q FcA) = 0 := by
    rw [← φ.comm, h0, map_zero]
  have hcls : (HomogeneousCochainIso.hcx (N.resSub U) G).cls q (φ.f q FcA) h1 =
      (HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0 :=
    congrArg (fun t => t ((HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0)) huq
  have hB : φ.f q FcA - FcA ∈ (HomogeneousCochainIso.hcx (N.resSub U) G).B q :=
    (Submodule.Quotient.eq (((HomogeneousCochainIso.hcx (N.resSub U) G).B q).comap
      ((HomogeneousCochainIso.hcx (N.resSub U) G).Z q).subtype)).mp hcls
  have hFr' : (φ.f q FcA).1 = fun z => CCA.homz N.rho q c.1 (fun i => ((retr U (z i) : U) : G)) := by
    funext z
    exact (hφ q FcA z).trans (congrFun hFcA _)

  have hrc : (N.resSub U).coch.d q ((Pair.res N U.subtype continuous_subtype_val).hom.f q c) = 0 := by
    rw [← (Pair.res N U.subtype continuous_subtype_val).hom.comm, hc', map_zero]
  obtain ⟨z1, hz1, hz1e, hz1c⟩ := hcupU p q a _ ha' hrc
  have hca : M.coch.d p (corM.f p a) = 0 := by rw [← corM.comm, ha', map_zero]
  obtain ⟨z2, hz2, hz2e, hz2c⟩ := hcup p q (corM.f p a) c hca hc'
  have hzz : P.coch.d (p + q) (corP.f (p + q) z1) = 0 := by rw [← corP.comm, hz1, map_zero]
  have hmem1 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (φ.f q FcA).1
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA) (hF' := (φ.f q FcA).2)
    rw [hβ] at h; exact h
  have hmem2 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (CCA.homz N.rho q c.1)
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA)
      (hF' := CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN))
    rw [hβ] at h; exact h

  have hD1 : (eP (p + q) (corP.f (p + q) z1)).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (φ.f q FcA).1) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := corP.f (p + q) z1)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem1)) (hf := fun g => ?_)
    rw [hcorP (p + q) z1, hz1e, hFr']
    exact CCA.cor_cup_eq (b := b) (bU := bU) (hb := hβ) (p := p) (q := q) (f := a.1) (f' := c.1)
      (g := g)
  have hD2 : (eP (p + q) z2).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (CCA.homz N.rho q c.1)) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := z2)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem2)) (hf := fun g => ?_)
    rw [hz2e, hcorM p a]
    exact CCA.cup_cor_eq (U := U) (b := b) (p := p) (q := q) (f := a.1) (f' := c.1) (g := g)

  have key : P.coch.cls (p + q) (corP.f (p + q) z1) hzz = P.coch.cls (p + q) z2 hz2 := by
    apply (Submodule.Quotient.eq (p := _)).mpr
    show corP.f (p + q) z1 - z2 ∈ P.coch.B (p + q)
    cases q with
    | zero =>
      have hz : φ.f 0 FcA = FcA := sub_eq_zero.mp ((Submodule.mem_bot (R := R)).mp hB)
      have hD : corP.f (p + 0) z1 - z2 = 0 := by
        apply (eP (p + 0)).injective
        apply Subtype.ext
        rw [map_sub, map_zero, Submodule.coe_sub, Submodule.coe_zero, hD1, hD2, hz, hFcA, sub_self]
      rw [hD]; exact Submodule.zero_mem _
    | succ q' =>
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hB
      have hwv : hd q' w.1 = (φ.f (q' + 1) FcA).1 - FcA.1 := congrArg Subtype.val hw
      rw [hFcA] at hwv
      have hh := CCA.hd_hcup b.β p q' _ w.1 hA0
      have hWmem : ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
          (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          ∈ hcoch P G (p + q') := by
        refine zsmul_mem (CCA.normF_mem (M := P) (U := U) (n := p + q') (hF := ?_)) _
        have h := CCA.hcup_mem (b := bU) (p := p) (q := q') (hF := hA) (hF' := w.2)
        rw [hβ] at h; exact h
      show corP.f (p + (q' + 1)) z1 - z2 ∈ LinearMap.range (P.coch.d (p + q'))
      refine LinearMap.mem_range.mpr ⟨(eP (p + q')).symm ⟨_, hWmem⟩, ?_⟩
      apply (eP (p + (q' + 1))).injective
      apply Subtype.ext
      refine (hPh (p + q') _).trans ?_
      rw [LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, hD1, hD2]
      exact calc hd (p + q') ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          = (-1 : ℤ) ^ p • hd (p + q') (CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            CCA.hd_zsmul _ _ _
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) (hd (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • F) (CCA.normF_hd (M := P) (U := U) (n := p + q') _).symm
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) ((-1 : ℤ) ^ p • CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) F) hh
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) := by
            rw [CCA.normF_zsmul, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (Sub.sub (α := (Fin (q' + 1 + 1) → G) → N.V) (φ.f (q' + 1) FcA).1
              (CCA.homz N.rho (q' + 1) c.1))) :=
            congrArg (fun F => CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) F)) hwv
        _ = _ := (congrArg (CCA.normF P U (p + q' + 1)) (CCA.hcup_sub_right b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
              (φ.f (q' + 1) FcA).1 (CCA.homz N.rho (q' + 1) c.1))).trans
            (CCA.normF_sub (M := P) (U := U) (n := p + q' + 1) _ _)
  have L : cupU p q ((M.resSub U).coch.cls p a ha')
      ((Pair.res N U.subtype continuous_subtype_val).hom.H q (N.coch.cls q c hc')) =
      (P.resSub U).coch.cls (p + q) z1 hz1 := hz1c
  have Rr : cup p q (corM.H p ((M.resSub U).coch.cls p a ha')) (N.coch.cls q c hc') =
      P.coch.cls (p + q) z2 hz2 := hz2c
  exact (congrArg (corP.H (p + q)) L).trans (key.trans Rr.symm)

end ReciprocityTheory.Coh

module

public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.MemMapAugmentationIdealComapPullbackQuotient
section -- merged from ReciprocityTheory.DualLattices.ExistsFamilyValuationDetEqOne
section -- merged from ReciprocityTheory.DualLattices.ValuationDetLeOneOfEntriesIntegral
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem hopfOrder_exists_algebraMap_eq_of_mem (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (x : N) :
    ∃ r : R, algebraMap R C r = f x := by
  exact AA.le_int hf x

theorem hopfOrder_translate_mem (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) (y : N) :
    (fun x => f (x + y)) ∈ AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      AA.carrier.comap (LinearMap.funLeft R C (fun x : N => (x, y))) := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := AA.le_int hh y
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : LinearMap.funLeft R C (fun x : N => (x, y)) (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x; simp [Algebra.smul_def, hr, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)

theorem coset_functional_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (φ : (K → C) →ₗ[C] C)
    (hφ : ∀ h ∈ AA.carrier.map (resK (R := R) K), ∃ r : R, algebraMap R C r = φ h)
    {f : N → C} (hf : f ∈ AA.carrier) :
    (fun x => φ (fun k : K => f (x + k))) ∈ AA.carrier := by
  let φR := φ.restrictScalars R
  let Ψ : (N × N → C) →ₗ[R] (N → C) :=
    (φR.compLeft N) ∘ₗ (LinearEquiv.curry R C N K).toLinearMap ∘ₗ
      LinearMap.funLeft R C (fun p : N × K => (p.1, (p.2 : N)))
  have key : tensorSpan R AA.carrier ≤ AA.carrier.comap Ψ := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := hφ (resK (R := R) K h) (Submodule.mem_map_of_mem hh)
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have e : Ψ (fun p : N × N => g p.1 * h p.2) = r • g := by
      ext x
      have : (fun k : K => g x * h k) = g x • resK (R := R) K h := by
        ext k; simp [resK]
      simp only [Ψ, φR, LinearMap.coe_comp, Function.comp_apply, LinearMap.compLeft_apply,
        LinearEquiv.coe_coe, LinearMap.restrictScalars_apply]
      show φ (fun k : K => g x * h k) = (r • g) x
      rw [this, φ.map_smul, ← hr]
      simp [Algebra.smul_def, mul_comm]
    rw [e]; exact AA.carrier.smul_mem r hg
  exact key (AA.comul f hf)

def h3co (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : N → C) (x : N) : K → C :=
  β⁻¹ *ᵥ fun k : K => f (x + k)

theorem cosetCoordinates_expand (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : N → C)
    (x : N) (k : K) : f (x + k) = ∑ l, β k l * h3co K β f x l := by
  have e : β *ᵥ (β⁻¹ *ᵥ fun k' : K => f (x + k')) = fun k' : K => f (x + k') := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hβ, Matrix.one_mulVec]
  exact (congrFun e k).symm

theorem exists_algebraMap_eq_inv_mulVec (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {h : K → C} (hh : h ∈ AA.carrier.map (resK (R := R) K)) (l : K) :
    ∃ r : R, algebraMap R C r = (β⁻¹ *ᵥ h) l := by
  rw [hAK] at hh
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    have e : β⁻¹ *ᵥ (fun k => β k j) = Pi.single j 1 := by
      ext l'
      have := congrFun (congrFun (Matrix.nonsing_inv_mul β hβ) l') j
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    rw [e]
    by_cases hl : l = j
    · exact ⟨1, by simp [hl]⟩
    · exact ⟨0, by simp [hl]⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨s, hs⟩ := hb
    exact ⟨r + s, by simp [Matrix.mulVec_add, hr, hs]⟩
  | smul c a _ ha =>
    obtain ⟨r, hr⟩ := ha
    exact ⟨c * r, by rw [Matrix.mulVec_smul]; simp [hr, Algebra.smul_def]⟩

theorem cosetCoordinates_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {f : N → C} (hf : f ∈ AA.carrier) (l : K) :
    (fun x => h3co K β f x l) ∈ AA.carrier := by
  exact coset_functional_mem AA K ((LinearMap.proj l).comp (Matrix.mulVecLin β⁻¹))
    (fun h hh => exists_algebraMap_eq_inv_mulVec AA K β hβ hAK hh l) hf

def h3T (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (k : K) : Matrix K K C :=
  Matrix.of fun l l' => (β⁻¹ *ᵥ fun k' : K => β (k + k') l) l'

theorem cosetCoordinates_add (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : N → C)
    (x : N) (k : K) : h3co K β f (x + k) = h3co K β f x ᵥ* h3T K β k := by
  ext l'
  have hw : (fun k' : K => f (x + k + k')) =
      ∑ l, h3co K β f x l • (fun k' : K => β (k + k') l) := by
    ext k'
    rw [show (x + (k : N) + (k' : N)) = x + ((k + k' : K) : N) by simp [add_assoc],
      cosetCoordinates_expand K β hβ f x (k + k')]
    simp [Finset.sum_apply, mul_comm]
  show (β⁻¹ *ᵥ fun k' : K => f (x + k + k')) l' = _
  rw [hw, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul,
    dotProduct, h3T, Matrix.of_apply]

theorem valuation_det_le_one_of_entries_integral (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X C) (hM : ∀ i j, ∃ r : R, algebraMap R C r = M i j) : v M.det ≤ 1 := by
  choose Mr hMr using hM
  have e : M = (algebraMap R C).mapMatrix (Matrix.of Mr) := by
    ext i j; simp [hMr]
  rw [e, ← RingHom.map_det]
  exact hv.map_le_one _

def h3mm (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : K → N → C) (x : N) : Matrix K K C :=
  Matrix.of fun j l => h3co K β (f j) x l

theorem cosetCoordinateMatrix_add (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : K → N → C)
    (x : N) (k : K) : h3mm K β f (x + k) = h3mm K β f x * h3T K β k := by
  ext j l'
  simp only [h3mm, Matrix.of_apply, Matrix.mul_apply]
  rw [cosetCoordinates_add K β hβ (f j) x k]
  simp [Matrix.vecMul, dotProduct]

theorem valuation_det_cosetCoordinateMatrix_add (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    (f : K → N → C) (x : N) (k : K) :
    v (h3mm K β f (x + k)).det = v (h3mm K β f x).det := by
  rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, map_mul]
  suffices h : v (h3T K β k).det = 1 by rw [h, mul_one]
  have hT : h3T K β k = (β⁻¹ * β.submatrix (Equiv.addLeft k) id)ᵀ := by
    ext l l'
    simp [h3T, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hT, Matrix.det_transpose, Matrix.det_mul, Matrix.det_permute, Matrix.det_nonsing_inv]
  have hd : β.det ≠ 0 := hβ.ne_zero
  have hs : v ((Equiv.Perm.sign (Equiv.addLeft k) : ℤ) : C) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.addLeft k)) with h | h <;>
      simp [h, Valuation.map_neg]
  rw [Ring.inverse_eq_inv', map_mul, map_mul, hs, one_mul, map_inv₀, inv_mul_cancel₀]
  exact (Valuation.ne_zero_iff v).mpr hd

def hopfOrderSubgroup (AA : HopfOrder (C := C) R N) : Subring (N → C) where
  carrier := AA.carrier
  mul_mem' := fun ha hb => AA.mul_mem _ _ ha hb
  one_mem' := AA.one_mem
  add_mem' := fun ha hb => AA.carrier.add_mem ha hb
  zero_mem' := AA.carrier.zero_mem
  neg_mem' := fun ha => AA.carrier.neg_mem ha

theorem det_mem_and_adjugate_mem (AA : HopfOrder (C := C) R N) {X : Type} [Fintype X] [DecidableEq X]
    (F : Matrix X X (N → C)) (hF : ∀ i j, F i j ∈ AA.carrier) :
    (fun x => (F.map fun g => g x).det) ∈ AA.carrier ∧
      ∀ i j, (fun x => (F.map fun g => g x).adjugate i j) ∈ AA.carrier := by
  let F' : Matrix X X (hopfOrderSubgroup AA) := Matrix.of fun i j => ⟨F i j, hF i j⟩
  have hF' : F = (hopfOrderSubgroup AA).subtype.mapMatrix F' := Matrix.ext fun i j => rfl
  refine ⟨?_, fun i j => ?_⟩
  · have e : (fun x => (F.map fun g => g x).det) = F.det := by
      funext x
      exact ((Pi.evalRingHom (fun _ : N => C) x).map_det F).symm
    rw [e, hF', ← RingHom.map_det]
    exact (F'.det).2
  · have e : (fun x => (F.map fun g => g x).adjugate i j) = F.adjugate i j := by
      funext x
      have := (Pi.evalRingHom (fun _ : N => C) x).map_adjugate F
      exact (congrFun (congrFun this i) j).symm
    rw [e, hF', ← RingHom.map_adjugate]
    exact (F'.adjugate i j).2

theorem cosetCoordinates_pullbackQuotient_mul (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (e : N ⧸ K → C) (f : N → C)
    (x : N) : h3co K β (pullQ (R := R) K e * f) x = e (x : N ⧸ K) • h3co K β f x := by
  have hE : (fun k : K => (pullQ (R := R) K e * f) (x + k)) =
      e (x : N ⧸ K) • fun k : K => f (x + k) := by
    ext k
    show e ((x + k : N) : N ⧸ K) * f (x + k) = e (x : N ⧸ K) * f (x + k)
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]
  show β⁻¹ *ᵥ (fun k : K => (pullQ (R := R) K e * f) (x + k)) = _
  rw [hE, Matrix.mulVec_smul]
  rfl

end ReciprocityTheory.PGsh.L2
end
end

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem cosetCoordinates_sum (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) {ι : Type}
    [Fintype ι] (g : ι → N → C) (x : N) :
    h3co K β (∑ i, g i) x = ∑ i, h3co K β (g i) x := by
  funext l
  simp only [h3co, Finset.sum_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

private theorem hopfOrder_prod_mem_carrier (AA : HopfOrder (C := C) R N) {ι : Type} (s : Finset ι)
    (g : ι → N → C) (h : ∀ i ∈ s, g i ∈ AA.carrier) : ∏ i ∈ s, g i ∈ AA.carrier := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using AA.one_mem
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact AA.mul_mem _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem hopfOrder_const_mem (AA : HopfOrder (C := C) R N) (r : R) :
    (fun _ : N => algebraMap R C r) ∈ AA.carrier := by
  have e : (fun _ : N => algebraMap R C r) = r • (1 : N → C) := by
    funext y
    simp [Algebra.smul_def]
  rw [e]
  exact AA.carrier.smul_mem r AA.one_mem

private theorem hopfOrder_const_sub_mem (AA : HopfOrder (C := C) R N) {n : N → C} (hn : n ∈ AA.carrier)
    (z : N) : (fun y => n z - n y) ∈ AA.carrier := by
  obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA hn z
  have e : (fun y => n z - n y) = (fun _ : N => algebraMap R C r) - n := by
    funext y
    simp [hr]
  rw [e]
  exact AA.carrier.sub_mem (hopfOrder_const_mem AA r) hn

private theorem h3co_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (F F' : N → C) (y : N) :
    h3co K β (a * F + b * F') y =
      a y • h3co K β F y + b y • h3co K β F' y := by
  simp only [h3co]
  have e : (fun k : K => (a * F + b * F') (y + k)) =
      a y • (fun k : K => F (y + k)) + b y • (fun k : K => F' (y + k)) := by
    funext k
    simp [ha, hb]
  rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

private theorem h3mm_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (G G' : K → N → C) (y : N) :
    h3mm K β (fun j => a * G j + b * G' j) y =
      a y • h3mm K β G y + b y • h3mm K β G' y := by
  ext j l
  simp only [h3mm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    h3co_mul_add_of_coset_invariant K β a b ha hb, Pi.add_apply, Pi.smul_apply]

private theorem hopfOrder_det_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => (h3mm K β G y).det) ∈ AA.carrier := by
  have h := (det_mem_and_adjugate_mem AA
    (Matrix.of fun i j => fun y => h3co K β (G i) y j)
    (fun i j => cosetCoordinates_mem AA K β hβ hAK (hG i) j)).1
  have e : ∀ y, (Matrix.of fun i j => fun y => h3co K β (G i) y j).map
      (fun g => g y) = h3mm K β G y := fun y => by
    ext i j
    rfl
  simpa only [e] using h

private theorem hopfOrder_norm_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => ∏ k : K, (h3mm K β G (y + k)).det) ∈ AA.carrier := by
  have e : (fun y => ∏ k : K, (h3mm K β G (y + k)).det) =
      ∏ k : K, (fun y => (h3mm K β G (y + k)).det) := by
    funext y
    simp only [Finset.prod_apply]
  rw [e]
  exact hopfOrder_prod_mem_carrier AA _ _ fun k _ =>
    hopfOrder_translate_mem AA (hopfOrder_det_fun_mem AA K β hβ hAK G hG) (k : N)

private theorem valuation_sub_eq_one_of_eq_one_of_lt_one {a b : C} (ha : v a = 1) (hb : v b < 1) :
    v (a - b) = 1 := by
  have h : v (-b) < v a := by
    rw [Valuation.map_neg, ha]
    exact hb
  rw [sub_eq_add_neg, v.map_add_eq_of_lt_left h, ha]

private theorem nnreal_pow_lt_one_of_lt_one_of_ne_zero {a : NNReal} (hlt : a < 1) {m : ℕ} (hm : m ≠ 0) :
    a ^ m < 1 := by
  have h0 : (0 : NNReal) ≤ a := by positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [pow_succ]
  refine lt_of_le_of_lt (mul_le_of_le_one_left h0 ?_) hlt
  exact pow_le_one₀ h0 hlt.le

theorem exists_family_valuation_det_eq_one (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j)) :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ x, v (h3mm K β f x).det = 1 := by
  classical
  have hlift : ∀ j : K, ∃ f ∈ AA.carrier, ∀ k : K, f k = β k j := by
    intro j
    have hmem : (fun k : K => β k j) ∈ AA.carrier.map (resK (R := R) K) := by
      rw [hAK]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp hmem
    exact ⟨f, hf, fun k => congrFun hfe k⟩
  choose f0 hf0 hf0e using hlift
  have hgood : ∀ x : N,
      v (h3mm K β (fun j y => f0 j (y + -x)) x).det = 1 := by
    intro x
    have e : h3mm K β (fun j y => f0 j (y + -x)) x = (β⁻¹ * β)ᵀ := by
      ext j l
      have h1 : (fun k : K => f0 j (x + (k : N) + -x)) = fun k => β k j := by
        funext k
        rw [show x + (k : N) + -x = k by abel]
        exact hf0e j k
      show (β⁻¹ *ᵥ fun k : K => f0 j (x + (k : N) + -x)) l = (β⁻¹ * β) l j
      rw [h1]
      rfl
    rw [e, Matrix.nonsing_inv_mul β hβ, Matrix.transpose_one, Matrix.det_one, map_one]
  have key : ∀ S : Finset N, ∃ G : K → N → C, (∀ j, G j ∈ AA.carrier) ∧
      ∀ z ∈ S, v (h3mm K β G z).det = 1 := by
    intro S
    refine Finset.induction_on S ⟨fun _ => 0, fun _ => AA.carrier.zero_mem, by simp⟩ ?_
    intro x S hx ih
    obtain ⟨G, hG, hS⟩ := ih
    by_cases hGx : v (h3mm K β G x).det = 1
    · refine ⟨G, hG, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with hzx | hz
      · rw [hzx]
        exact hGx
      · exact hS z hz
    obtain ⟨n, hn_def⟩ : ∃ n : N → C,
        n = fun y => ∏ k : K, (h3mm K β G (y + k)).det := ⟨_, rfl⟩
    have hnmem : n ∈ AA.carrier := by
      rw [hn_def]
      exact hopfOrder_norm_fun_mem AA K β hβ hAK G hG
    have hninv : ∀ y (k0 : K), n (y + k0) = n y := by
      intro y k0
      simp only [hn_def]
      exact Fintype.prod_equiv (Equiv.addLeft k0) _ _ (fun k => by simp [add_assoc])
    have hvn : ∀ y, v (n y) = v (h3mm K β G y).det ^ Fintype.card K := by
      intro y
      simp only [hn_def]
      rw [map_prod, Finset.prod_congr rfl (fun k _ =>
        valuation_det_cosetCoordinateMatrix_add hv AA K β hβ hAK G y k),
        Finset.prod_const, Finset.card_univ]
    have hDle : ∀ y, v (h3mm K β G y).det ≤ 1 := fun y =>
      valuation_det_le_one_of_entries_integral hv _ (fun i j =>
        hopfOrder_exists_algebraMap_eq_of_mem AA (cosetCoordinates_mem AA K β hβ hAK (hG i) j) y)
    have : Nonempty K := ⟨0⟩
    have hcard : Fintype.card K ≠ 0 := Fintype.card_ne_zero
    have hnS : ∀ z ∈ S, v (n z) = 1 := fun z hz => by
      rw [hvn, hS z hz, one_pow]
    have hnx : v (n x) < 1 := by
      rw [hvn]
      exact nnreal_pow_lt_one_of_lt_one_of_ne_zero (lt_of_le_of_ne (hDle x) hGx) hcard
    obtain ⟨a, ha_def⟩ : ∃ a : N → C, a = fun y => n x - n y := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : N → C, b = fun y => ∏ w ∈ S, (n w - n y) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : K → N → C, g = fun j y => f0 j (y + -x) := ⟨_, rfl⟩
    have hamem : a ∈ AA.carrier := by
      rw [ha_def]
      exact hopfOrder_const_sub_mem AA hnmem x
    have hbmem : b ∈ AA.carrier := by
      have e : (fun y => ∏ w ∈ S, (n w - n y)) = ∏ w ∈ S, (fun y => n w - n y) := by
        funext y
        simp only [Finset.prod_apply]
      rw [hb_def, e]
      exact hopfOrder_prod_mem_carrier AA S _ (fun w _ => hopfOrder_const_sub_mem AA hnmem w)
    have hgmem : ∀ j, g j ∈ AA.carrier := by
      intro j
      rw [hg_def]
      exact hopfOrder_translate_mem AA (hf0 j) (-x)
    have hgx : v (h3mm K β g x).det = 1 := by
      rw [hg_def]
      exact hgood x
    have hainv : ∀ y (k : K), a (y + k) = a y := by
      intro y k
      simp only [ha_def, hninv]
    have hbinv : ∀ y (k : K), b (y + k) = b y := by
      intro y k
      simp only [hb_def, hninv]
    refine ⟨fun j => a * G j + b * g j, fun j => AA.carrier.add_mem
      (AA.mul_mem _ _ hamem (hG j)) (AA.mul_mem _ _ hbmem (hgmem j)), fun z hz => ?_⟩
    rw [h3mm_mul_add_of_coset_invariant K β a b hainv hbinv G g z]
    rcases Finset.mem_insert.mp hz with hzx | hz
    · rw [hzx]
      have ha0 : a x = 0 := by simp only [ha_def, sub_self]
      have hb1 : v (b x) = 1 := by
        simp only [hb_def]
        rw [map_prod]
        exact Finset.prod_eq_one (fun w hw => valuation_sub_eq_one_of_eq_one_of_lt_one (hnS w hw) hnx)
      rw [ha0, zero_smul, zero_add, Matrix.det_smul, map_mul, map_pow, hgx, hb1, one_pow,
        mul_one]
    · have hb0 : b z = 0 := by
        simp only [hb_def]
        exact Finset.prod_eq_zero hz (sub_self _)
      have ha1 : v (a z) = 1 := by
        simp only [ha_def]
        rw [Valuation.map_sub_swap]
        exact valuation_sub_eq_one_of_eq_one_of_lt_one (hnS z hz) hnx
      rw [hb0, zero_smul, add_zero, Matrix.det_smul, map_mul, map_pow, hS z hz, ha1, one_pow,
        mul_one]
  obtain ⟨G, hG, hGall⟩ := key Finset.univ
  exact ⟨G, hG, fun x => hGall x (Finset.mem_univ x)⟩

end ReciprocityTheory.PGsh.L2
end
end

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem apply_add_of_mem_map_pullbackQuotient (K : AddSubgroup N) (M : Submodule R (N ⧸ K → C)) {h : N → C}
    (hh : h ∈ M.map (pullQ (R := R) K)) (x : N) (k : K) : h (x + k) = h x := by
  obtain ⟨u, -, rfl⟩ := hh
  simp only [pullQ, LinearMap.funLeft_apply]
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]

theorem pullbackQuotient_apply_out (K : AddSubgroup N) {h : N → C} (hinv : ∀ x (k : K), h (x + k) = h x) :
    pullQ (R := R) K (fun q => h q.out) = h := by
  funext x
  simp only [pullQ, LinearMap.funLeft_apply]
  have e : (((QuotientAddGroup.mk x : N ⧸ K).out : N) : N ⧸ K) = (x : N ⧸ K) := by
    exact Quotient.out_eq _
  have hk := QuotientAddGroup.eq.mp e
  calc h (QuotientAddGroup.mk x : N ⧸ K).out
      = h ((QuotientAddGroup.mk x : N ⧸ K).out + ((⟨_, hk⟩ : K) : N)) := (hinv _ _).symm
    _ = h x := by congr 1; simp

theorem mem_map_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) :
    h ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
  exact hh

theorem mem_map_augmentationIdeal_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) (h0 : h 0 = 0) :
    h ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  simp only [augIdeal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
    exact hh
  · have h1 := congrFun (pullbackQuotient_apply_out (R := R) K hinv) 0
    simp only [pullQ, LinearMap.funLeft_apply, QuotientAddGroup.mk_zero] at h1
    simp only [LinearMap.mem_ker, LinearMap.proj_apply]
    rw [h1, h0]

section family

variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)

include hβ hdet in
theorem eq_zero_of_sum_mul_coset_eq_zero (x : N) (c : K → C) (h : ∀ k : K, ∑ j, c j * f j (x + k) = 0) : c = 0 := by
  have hM : (h3mm K β f x).det ≠ 0 := by
    intro h0
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hw : β *ᵥ (c ᵥ* h3mm K β f x) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h k]
    have e : ∀ j, f j (x + k) = ∑ l, β k l * h3mm K β f x j l := fun j => by
      rw [cosetCoordinates_expand K β hβ (f j) x k]
      rfl
    simp only [e]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hw0 : c ᵥ* h3mm K β f x = 0 := by
    have := congrArg (β⁻¹ *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul β hβ] using this
  by_contra hc
  exact hM (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc, hw0⟩)

include hv hβ hAK hf hdet in
theorem exists_coset_invariant_coefficients {g : N → C} (hg : g ∈ AA.carrier) :
    ∃ b : K → N → C, (∀ j, b j ∈ AA.carrier) ∧ (∀ j x (k : K), b j (x + k) = b j x) ∧
      g = ∑ j, b j * f j := by
  have hDne : ∀ x, (h3mm K β f x).det ≠ 0 := fun x h0 => by
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hFu : ∀ x, IsUnit (h3mm K β f x).det := fun x =>
    isUnit_iff_ne_zero.mpr (hDne x)
  obtain ⟨b, hb⟩ : ∃ b : K → N → C, b = fun j x =>
      (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j := ⟨_, rfl⟩
  have hbx : ∀ j x, b j x = (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j :=
    fun j x => by rw [hb]
  let Fm : Matrix K K (N → C) := Matrix.of fun i j => fun x => h3co K β (f i) x j
  have hFm : ∀ i j, Fm i j ∈ AA.carrier := fun i j =>
    cosetCoordinates_mem AA K β hβ hAK (hf i) j
  have hDA := det_mem_and_adjugate_mem AA Fm hFm
  have hD : (fun x => (h3mm K β f x).det) ∈ AA.carrier := hDA.1
  have hAdj : ∀ l j, (fun x => (h3mm K β f x).adjugate l j) ∈ AA.carrier :=
    hDA.2
  obtain ⟨P, hP, hA⟩ := AA.lat
  have hDinv : (fun x => (h3mm K β f x).det)⁻¹ ∈ AA.carrier :=
    inv_mem_of_valuation_eq_one hv AA.carrier P hP hA AA.one_mem AA.mul_mem _ hD hdet
  have hG : ∀ l, (fun x => h3co K β g x l) ∈ AA.carrier := fun l =>
    cosetCoordinates_mem AA K β hβ hAK hg l
  refine ⟨b, ?_, ?_, ?_⟩
  · intro j
    have key : b j = (∑ l, (fun x => h3co K β g x l) *
        (fun x => (h3mm K β f x).adjugate l j)) *
        (fun x => (h3mm K β f x).det)⁻¹ := by
      funext x
      rw [hbx, Matrix.inv_def]
      simp only [Pi.mul_apply, Finset.sum_apply, Pi.inv_apply, Matrix.vecMul, dotProduct,
        Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Ring.inverse_eq_inv]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key]
    exact AA.mul_mem _ _ (Submodule.sum_mem _ fun l _ => AA.mul_mem _ _ (hG l) (hAdj l j)) hDinv
  · intro j x k
    have hT : IsUnit (h3T K β k).det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hDne (x + k) ?_
      rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, h0, mul_zero]
    rw [hbx, hbx, cosetCoordinates_add K β hβ g x k, cosetCoordinateMatrix_add K β hβ f x k,
      Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hT, Matrix.one_mul]
  · funext x
    have e1 := cosetCoordinates_expand K β hβ g x 0
    have e2 := fun j => cosetCoordinates_expand K β hβ (f j) x 0
    rw [show ((0 : K) : N) = 0 from rfl, add_zero] at e1
    simp only [show ((0 : K) : N) = 0 from rfl, add_zero] at e2
    have hv' : (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) ᵥ*
        h3mm K β f x = h3co K β g x := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hFu x), Matrix.vecMul_one]
    have hw : ∀ l, ∑ j, (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j *
        h3co K β (f j) x l = h3co K β g x l := fun l => by
      have := congrFun hv' l
      exact this
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hbx, e2]
    rw [e1]
    generalize h3co K β g x ᵥ* (h3mm K β f x)⁻¹ = w at hw ⊢
    simp only [← hw]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end family

end ReciprocityTheory.PGsh.L2
end
end

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem exists_basis_map_restrictToSubgroup (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩

theorem exists_coset_basis (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)

theorem mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)

private theorem mem_augIdeal_iff {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal]

theorem mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  intro g hgI hres
  have hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0 := mem_augIdeal_iff _
  have hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier :=
    Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1
  have hle : augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤
      (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨⟨a, ha, rfl⟩, hp0⟩ := (mem_augIdeal_iff _ _).1 hp
    obtain ⟨⟨b, hb, rfl⟩, hq0⟩ := (mem_augIdeal_iff _ _).1 hq
    refine ⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩
    · simpa [resK] using hp0
    · simpa [resK] using hq0
    · funext k; simp [resK]
  obtain ⟨q, hq, hqg⟩ := hle hres
  have hgq : g - q ∈ AA.carrier := AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)
  have hker := mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])
  have hmul : (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
    refine Submodule.mul_le.mpr fun e he a ha => ?_
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨he'A, he'0⟩ := (mem_augIdeal_iff _ _).1 he'
    obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA ha 0
    have heI : pullQ (R := R) K e' ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩
    have haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem),
        by simp [Algebra.smul_def, hr]⟩
    have hsplit : pullQ (R := R) K e' * a =
        pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by
      rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI))
      (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))
  have hg : g = (g - q) + q := by abel
  rw [hg]
  exact Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)

end ReciprocityTheory.PGsh.L2

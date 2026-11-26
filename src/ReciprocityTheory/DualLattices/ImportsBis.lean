module

public import ReciprocityTheory.DualLattices.MemSupOfRestrictToSubgroupMemSq
public import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.ImportsBis
section -- merged from ReciprocityTheory.DualLattices.HasColengthEqPowMulPow
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem quotient_out_add_coe (K : AddSubgroup N) (q : N ⧸ K) (k : K) :
    ((q.out + k : N) : N ⧸ K) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (k : N)).mpr k.2, add_zero]

def quotientProdSubgroupEquiv (K : AddSubgroup N) : (N ⧸ K) × K ≃ N where
  toFun p := p.1.out + p.2
  invFun x := ((x : N ⧸ K),
    ⟨-((x : N ⧸ K).out) + x, QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)⟩)
  left_inv := by
    rintro ⟨q, k⟩
    refine Prod.ext (quotient_out_add_coe K q k) (Subtype.ext ?_)
    show -((((q.out + k : N)) : N ⧸ K).out) + (q.out + k) = k
    rw [quotient_out_add_coe K q k]
    abel
  right_inv := by
    intro x
    show (x : N ⧸ K).out + (-((x : N ⧸ K).out) + x) = x
    abel

private theorem valuation_det_le_one_of_integral_entries (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (E : Matrix X X C) (hE : ∀ i j, ∃ r : R, algebraMap R C r = E i j) : v E.det ≤ 1 := by
  choose M hM using hE
  have hEM : E = (Matrix.of M).map (algebraMap R C) := by
    ext i j
    exact (hM i j).symm
  rw [hEM, det_map_algebraMap]
  exact hv.map_le_one _

theorem hasColength_eq_pow_mul_pow (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)] :
    ∀ c cB cK, HasColen R v AA.carrier c →
      HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB →
      HasColen R v (AA.carrier.map (resK (R := R) K)) cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro c cB cK hc hcB hcK
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hfA, hfu⟩ := exists_coset_basis hv AA K
  obtain ⟨g, hgA, hgdet⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨P, hP, rfl⟩ := hc
  obtain ⟨Q, hQ, rfl⟩ := hcB
  obtain ⟨β', hβ', rfl⟩ := hcK
  obtain ⟨P0, hP0, hAP0⟩ := AA.lat
  have hint : ∀ {F : N → C}, F ∈ AA.carrier → ∀ x, ∃ r : R, algebraMap R C r = F x :=
    fun hF x => AA.le_int hF x
  have hK : v β'.det = v β.det := valuation_det_eq_of_span_eq_alt hv hβ (hAK.symm.trans hβ')
  have hmm1 : ∀ x, v (h3mm K β f x).det = 1 := by
    intro x
    have hdec : ∀ l, ∃ e : K → N ⧸ K → C,
        (∀ j, e j ∈ AA.carrier.comap (pullQ (R := R) K)) ∧
          g l = ∑ j, pullQ (R := R) K (e j) * f j := by
      intro l
      obtain ⟨b, ⟨hb, hgb⟩, -⟩ := hfu (g l) (hgA l)
      choose e he hbe using fun j => Submodule.mem_map.mp (hb j)
      refine ⟨e, he, ?_⟩
      rw [hgb]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]
    choose e he hge using hdec
    let Bx : Matrix K K C := Matrix.of fun l j => e l j (x : N ⧸ K)
    have hmul : h3mm K β g x = Bx * h3mm K β f x := by
      ext l m
      simp only [h3mm, Matrix.of_apply, Matrix.mul_apply, Bx]
      rw [hge l, cosetCoordinates_sum, Finset.sum_apply]
      simp only [cosetCoordinates_pullbackQuotient_mul, Pi.smul_apply, smul_eq_mul]
    have hB1 : v Bx.det ≤ 1 := valuation_det_le_one_of_integral_entries hv Bx fun l j => by
      obtain ⟨r, hr⟩ := hint (Submodule.mem_comap.mp (he l j)) x
      exact ⟨r, hr⟩
    have hF1 : v (h3mm K β f x).det ≤ 1 := valuation_det_le_one_of_integral_entries hv _ fun j m =>
      hint (cosetCoordinates_mem AA K β hβ hAK (hfA j) m) x
    have h := hgdet x
    rw [hmul, Matrix.det_mul, map_mul, mul_comm] at h
    exact eq_one_of_le_one_of_mul_eq_one hF1 hB1 h
  let e : K × (N ⧸ K) ≃ N := (Equiv.prodComm _ _).trans (quotientProdSubgroupEquiv K)
  have he_apply : ∀ p : K × (N ⧸ K), e p = p.2.out + p.1 := fun p => rfl
  let Φ : Matrix N N C := fun x n => Q (x : N ⧸ K) (e.symm n).2 * f (e.symm n).1 x
  have hspan : AA.carrier = Submodule.span R (Set.range fun n x => Φ x n) := by
    apply le_antisymm
    · intro G hG
      obtain ⟨b, ⟨hb, hGb⟩, -⟩ := hfu G hG
      rw [hGb]
      refine sum_mem fun j _ => ?_
      obtain ⟨b', hb', hbb'⟩ := Submodule.mem_map.mp (hb j)
      rw [hQ] at hb'
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hbb', ← hr, map_sum, Finset.sum_mul]
      refine sum_mem fun s _ => ?_
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e (j, s), ?_⟩)
      funext x
      simp only [Φ, Equiv.symm_apply_apply]
      rfl
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      have h1 : (fun q : N ⧸ K => Q q (e.symm n).2) ∈ AA.carrier.comap (pullQ (R := R) K) := by
        rw [hQ]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact AA.mul_mem _ _ h1 (hfA _)
  have hdetΦ : v Φ.det = v Q.det ^ Fintype.card K * v β.det ^ Fintype.card (N ⧸ K) := by
    rw [← Matrix.det_submatrix_equiv_self e Φ]
    have hblk : Φ.submatrix e e = Matrix.blockDiagonal (fun q : N ⧸ K =>
        β * (h3mm K β f q.out)ᵀ) * Matrix.kroneckerMap (· * ·) (1 : Matrix K K C) Q := by
      ext ⟨k, q⟩ ⟨j, s⟩
      show Q ((e (k, q) : N) : N ⧸ K) (e.symm (e (j, s))).2 * f (e.symm (e (j, s))).1 (e (k, q)) = _
      rw [Equiv.symm_apply_apply, he_apply]
      dsimp only
      rw [quotient_out_add_coe K q k, cosetCoordinates_expand K β hβ (f j) q.out k, Matrix.mul_apply]
      simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      conv_rhs => rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
      simp only [eq_self_iff_true, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      rw [mul_comm]
      rfl
    have hq : ∀ q : N ⧸ K, v (β * (h3mm K β f q.out)ᵀ).det = v β.det := by
      intro q
      rw [Matrix.det_mul, Matrix.det_transpose, map_mul, hmm1, mul_one]
    rw [hblk, Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_kronecker, Matrix.det_one,
      one_pow, one_mul, map_mul, map_prod, map_pow]
    simp only [hq, Finset.prod_const, Finset.card_univ]
    ring
  have h1 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hP)
  have h2 := valuation_det_eq_of_span_eq_alt hv hP0 (hAP0.symm.trans hspan)
  rw [h1, ← h2, hdetΦ, hK]

end ReciprocityTheory.PGsh.L2
end
end

section -- merged from ReciprocityTheory.DualLattices.SubgroupFreenessStatement
noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupFreenessStatement : Prop :=
  IsAlgClosed C → CharZero C →
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    let B := AA.carrier.comap (pullQ (R := R) K)
    let AK := AA.carrier.map (resK (R := R) K)
    let IK := (augIdeal B).map (pullQ K)
    (∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ B.map (pullQ K)) ∧ g = ∑ j, b j * f j) ∧
    (∀ g ∈ AA.carrier, resK (R := R) K g = 0 → g ∈ IK * AA.carrier) ∧
    (∀ c cB cK, HasColen R v AA.carrier c → HasColen R v B cB → HasColen R v AK cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K)) ∧
    (∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈ augIdeal AK * augIdeal AK →
      g ∈ IK ⊔ augIdeal AA.carrier * augIdeal AA.carrier)

end ReciprocityTheory.PGsh.L2
end
end

namespace ReciprocityTheory.PGsh.L2

theorem h3 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩

end ReciprocityTheory.PGsh.L2
end

section -- merged from ReciprocityTheory.DualLattices.CokernelLengthComparisonStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def tPart {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
    [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a : O) : Submodule R (Ix g → R) :=
  LinearMap.range (Matrix.mulVecLin ((H.ρ a).map (algebraMap ℤ_[p] R)))

def lieDPart {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
    [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a : O) : Submodule R (Fin g → R) :=
  LinearMap.range (Matrix.mulVecLin (H.ρL a)ᵀ)

abbrev htCoker {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a b : O) :=
  lieDPart H a ⧸ ((tPart H b).map (Matrix.mulVecLin H.Ht)).comap (lieDPart H a).subtype

def CokernelLengthComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb → cwb ≤ cw

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.UnramifiedCokernelLengthStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

abbrev cokE {g : ℕ} {R : Type} [CommRing R] {m : ℕ} (Ht : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT j))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype

structure UnramData (p : ℕ) [Fact p.Prime] (g : ℕ) {C : Type} [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O]
    [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) (H : HodgeTateDatum p g v R O σ cp) where
  m : ℕ
  sg : Fin m → (O →+* R)
  εT : Fin m → Matrix (Ix g) (Ix g) R
  εL : Fin m → Matrix (Fin g) (Fin g) R
  cj : Equiv.Perm (Fin m)
  φ : Equiv.Perm (Fin m)
  r : Fin m → ℕ
  noPad : H.P = 0 ∧ H.PL = 0
  εT_orth : ∀ i j, εT i * εT j = if i = j then εT i else 0
  εT_sum : ∑ i, εT i = 1
  εL_orth : ∀ i j, εL i * εL j = if i = j then εL i else 0
  εL_sum : ∑ i, εL i = 1
  εT_eig : ∀ a i, (H.ρ a).map (algebraMap ℤ_[p] R) * εT i = sg i a • εT i
  εL_eig : ∀ a i, H.ρL a * εL i = sg i a • εL i
  conj : ∀ i a, sg (cj i) a = sg i (σ a)
  frob : ∀ i a, v (algebraMap R C (sg (φ i) a - sg i a ^ p)) < 1
  distinct : ∀ i j, i ≠ j → ∃ a, v (algebraMap R C (sg i a - sg j a)) = 1
  rank : ∀ i, Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin (r i) → R))

def frobSum {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) : ℝ :=
  ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * U.r ((U.φ ^ (n + 1)) i)

def UnramifiedCokernelLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (V1 V2 : NNReal),
    HasLen v R (cokE H.Ht U.εT U.εL i (U.cj i)) V1 →
    HasLen v R (cokE H.Ht U.εT U.εL (U.cj i) i) V2 →
    (V1 : ℝ) = V2 * (v (algebraMap R C (p : R)) : ℝ) ^
      ((U.r i : ℝ) / (p - 1) - frobSum U i)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ValuationFourierLeOne
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem fourier_apply' {X H : Type} [Fintype X] (e : H → X → C) (u : X → C) (h : H) :
    fourier (R := R) e u h = ∑ a, u a * e h a := rfl

def pairInt {X : Type} [Fintype X] (U : X → C) : Submodule R (X → C) where
  carrier := {F | ∃ r : R, algebraMap R C r = ∑ x, U x * F x}
  add_mem' := by
    rintro F G ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by simp [hr, hs, mul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c F ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def conv (u w : N → C) : N → C := fun c => ∑ a, u a * w (c - a)

theorem fourier_conv {H : Type} (χ : H → AddChar N C) (u w : N → C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (conv u w) h =
      fourier (R := R) (fun h a => χ h a) u h * fourier (R := R) (fun h a => χ h a) w h := by
  rw [fourier_apply' (R := R), fourier_apply' (R := R), fourier_apply' (R := R),
    Finset.sum_mul_sum]
  simp only [conv, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.subRight a) _ _ fun c => ?_
  simp only [Equiv.subRight_apply]
  have hc : χ h c = χ h a * χ h (c - a) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring

private theorem mem_dualLat_iff_sum_mul_integral {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

private theorem mem_pairInt_iff {X : Type} [Fintype X] (U F : X → C) :
    F ∈ pairInt (R := R) U ↔ ∃ r : R, algebraMap R C r = ∑ x, U x * F x :=
  Iff.rfl

theorem conv_mem_dualLat (AA : HopfOrder (C := C) R N) {u w : N → C}
    (hu : u ∈ dualLat AA.carrier) (hw : w ∈ dualLat AA.carrier) :
    conv u w ∈ dualLat AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      pairInt (R := R) (fun p : N × N => u p.1 * w p.2) := by
    rw [tensorSpan, Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_pairInt_iff]
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hu g hg
    obtain ⟨s, hs⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hw k hk
    refine ⟨r * s, ?_⟩
    rw [map_mul, hr, hs, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := (mem_pairInt_iff _ _).1 (key (AA.comul f hf))
  refine ⟨r, hr.trans ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [addPull, LinearMap.funLeft_apply, conv, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => ?_
  simp

theorem single_mem_dualLat (AA : HopfOrder (C := C) R N) :
    (Pi.single 0 1 : N → C) ∈ dualLat AA.carrier := by
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := AA.le_int hf 0
  refine ⟨r, ?_⟩
  rw [hr]
  simp [Pi.single_apply]

def cpow (u : N → C) : ℕ → N → C
  | 0 => Pi.single 0 1
  | k + 1 => conv (cpow u k) u

theorem cpow_mem (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ dualLat AA.carrier) :
    ∀ k, cpow u k ∈ dualLat AA.carrier
  | 0 => single_mem_dualLat AA
  | k + 1 => conv_mem_dualLat AA (cpow_mem AA hu k) hu

theorem fourier_single {H : Type} (χ : H → AddChar N C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (Pi.single 0 1) h = 1 := by
  rw [fourier_apply' (R := R)]
  simp [Pi.single_apply]

theorem fourier_cpow {H : Type} (χ : H → AddChar N C) (u : N → C) (h : H) :
    ∀ k, fourier (R := R) (fun h a => χ h a) (cpow u k) h =
      fourier (R := R) (fun h a => χ h a) u h ^ k
  | 0 => by rw [pow_zero]; exact fourier_single χ h
  | k + 1 => by
    simp only [cpow]
    rw [fourier_conv, fourier_cpow χ u h k, pow_succ]

private theorem nnreal_le_one_of_forall_pow_le {x M : NNReal} (h : ∀ k : ℕ, x ^ k ≤ M) : x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hx
  exact (not_lt.2 (h k)) hk

private theorem le_sum_sum {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ → NNReal) (i : ι)
    (j : κ) : f i j ≤ ∑ i, ∑ j, f i j :=
  (Finset.single_le_sum (f := fun j => f i j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, f i j) (fun _ _ => zero_le) (Finset.mem_univ i))

private theorem hopfOrder_exists_valuation_apply_le (v : Valuation C NNReal) (hv : v.Integers R)
    (AA : HopfOrder (C := C) R N) :
    ∃ M : NNReal, ∀ u ∈ dualLat AA.carrier, ∀ a, v (u a) ≤ M := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  refine ⟨∑ j, ∑ x, v (B⁻¹ j x), fun u hu a => ?_⟩
  rw [hA, mem_dualLat_spanCols_iff] at hu
  have hu' : u = (u ᵥ* B) ᵥ* B⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  rw [hu']
  change v (∑ j, (u ᵥ* B) j * B⁻¹ j a) ≤ _
  apply v.map_sum_le
  intro j _
  obtain ⟨r, hr⟩ := hu j
  rw [map_mul, ← hr]
  exact (mul_le_of_le_one_left (zero_le) (hv.map_le_one r)).trans
    (le_sum_sum (fun j x => v (B⁻¹ j x)) j a)

theorem valuation_fourier_le_one (v : Valuation C NNReal) (hv : v.Integers R) {H : Type}
    (χ : H → AddChar N C) (AA : HopfOrder (C := C) R N) {u : N → C}
    (hu : u ∈ dualLat AA.carrier) (h : H) :
    v (fourier (R := R) (fun h a => χ h a) u h) ≤ 1 := by
  obtain ⟨M, hM⟩ := hopfOrder_exists_valuation_apply_le v hv AA
  have hχ : ∀ a, v (χ h a) ≤ 1 := fun a =>
    nnreal_le_one_of_forall_pow_le (M := ∑ b, v (χ h b)) fun k => by
      rw [← map_pow, ← AddChar.map_nsmul_eq_pow]
      exact Finset.single_le_sum (f := fun b => v (χ h b)) (fun _ _ => zero_le)
        (Finset.mem_univ _)
  apply nnreal_le_one_of_forall_pow_le (M := M)
  intro k
  rw [← map_pow, ← fourier_cpow (R := R) χ u h k, fourier_apply' (R := R)]
  apply v.map_sum_le
  intro a _
  rw [map_mul]
  exact (mul_le_of_le_one_right (zero_le) (hχ a)).trans
    (hM _ (cpow_mem AA hu k) a)

end ReciprocityTheory.PGsh.L2
end
end

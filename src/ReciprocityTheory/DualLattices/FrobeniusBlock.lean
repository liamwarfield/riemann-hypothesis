module

public import ReciprocityTheory.DualLattices.TowerZeroSurjective

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.FormMonomialUnitVector
section -- merged from ReciprocityTheory.DualLattices.ProdPowUnitVectorVal
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def e1 (l : Ix g) : Nb p g := Pi.single l 1

def hvec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R := uR hv D j y ^ p

def bR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) : Nb p g → R :=
  (MuR hv D)⁻¹ *ᵥ hvec hv D j

def epow (D : Lifts H U X) (α : Nb p g) : R := ∏ j, D.ε j ^ (α j).val

theorem unitVector_val (l j : Ix g) : ((e1 (p := p) l) j).val = if j = l then 1 else 0 := by
  unfold e1
  by_cases h : j = l
  · subst h
    simp [ZMod.val_one]
  · simp [Pi.single_apply, h]

theorem prod_pow_unitVector_val {M : Type} [CommMonoid M] (f : Ix g → M) (l : Ix g) :
    ∏ j, f j ^ ((e1 (p := p) l) j).val = f l := by
  simp only [unitVector_val]
  rw [Finset.prod_eq_single l (fun j _ hj => by rw [if_neg hj, pow_zero]) (by simp), if_pos rfl,
    pow_one]

theorem liftScalePow_unitVector (D : Lifts H U X) (l : Ix g) : epow D (e1 (p := p) l) = D.ε l := by
  exact prod_pow_unitVector_val D.ε l

theorem MuR_mulVec_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j : Ix g) : MuR hv D *ᵥ bR hv D j = hvec hv D j := by
  rw [bR, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_MuR hv hp1 D),
    Matrix.one_mulVec]

theorem mulVec_inj (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    {a b : Nb p g → R} (h : MuR hv D *ᵥ a = MuR hv D *ᵥ b) : a = b := by
  have h1 := congrArg (fun w => (MuR hv D)⁻¹ *ᵥ w) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_MuR hv hp1 D),
    Matrix.one_mulVec] using h1

theorem linX_xp (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) :
    linX D (fun y => xL D j y ^ p) l =
      algebraMap R C (bR hv D j (e1 l)) * (algebraMap R C (D.ε j) ^ p / algebraMap R C (D.ε l)) := by
  have hdet := det_valM_ne hv hp1 D
  have hE : ∀ α, algebraMap R C (epow D α) ≠ 0 := by
    intro α
    simp only [epow, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      pow_ne_zero _ (fun h0 => D.ε_ne j (hv.hom_inj (h0.trans (map_zero _).symm)))
  have hf : (fun y => xL D j y ^ p) = valM D *ᵥ (fun α => algebraMap R C (D.ε j) ^ p *
      algebraMap R C (bR hv D j α) / algebraMap R C (epow D α)) := by
    funext y
    simp only [Matrix.mulVec, dotProduct, valM_eq hv D, Matrix.mul_diagonal, Matrix.map_apply]
    have h2 := congrFun (MuR_mulVec_bR hv hp1 D j) y
    simp only [Matrix.mulVec, dotProduct, hvec] at h2
    have h3 := congrArg (algebraMap R C) h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_pow, uR_spec] at h3
    simp only [map_mul] at h3
    rw [xL, mul_pow, ← h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h4 := hE α
    simp only [epow] at h4 ⊢
    field_simp
  unfold linX coefX
  rw [hf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]
  show algebraMap R C (D.ε j) ^ p * algebraMap R C (bR hv D j (e1 l)) /
    algebraMap R C (epow D (e1 l)) = _
  rw [liftScalePow_unitVector]
  ring

def psi (a : O) (y : Nb p g) : Nb p g := ((H.ρ a).map PadicInt.toZMod) *ᵥ y

theorem red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by simp [red]⟩

theorem u_psi (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    D.u j (psi (H := H) (D.b k) y) = algebraMap R C (U.sg (D.κ j) (D.b k)) * D.u j y := by
  obtain ⟨t, rfl⟩ := red_surj y
  have h := D.eig j k t
  rw [red_mulVec] at h
  exact h

theorem uR_psi (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    uR hv D j (psi (H := H) (D.b k) y) = U.sg (D.κ j) (D.b k) * uR hv D j y := by
  apply hv.hom_inj
  rw [uR_spec, map_mul, uR_spec, u_psi]

theorem bR_eig (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j : Ix g) (k : Fin D.s) (α : Nb p g) :
    (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α =
      U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α := by
  have key : MuR hv D *ᵥ (fun α => (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α) =
      MuR hv D *ᵥ (fun α => U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α) := by
    funext y
    have h1 := congrFun (MuR_mulVec_bR hv hp1 D j) (psi (H := H) (D.b k) y)
    have h2 := congrFun (MuR_mulVec_bR hv hp1 D j) y
    simp only [Matrix.mulVec, dotProduct, MuR, Matrix.of_apply, hvec] at h1 h2 ⊢
    simp only [uR_psi, mul_pow, Finset.prod_mul_distrib] at h1
    calc ∑ α, (∏ j', uR hv D j' y ^ (α j').val) *
          ((∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * bR hv D j α)
        = ∑ α, (∏ j', U.sg (D.κ j') (D.b k) ^ (α j').val) * (∏ j', uR hv D j' y ^ (α j').val) *
            bR hv D j α := Finset.sum_congr rfl fun α _ => by ring
      _ = U.sg (D.κ j) (D.b k) ^ p * uR hv D j y ^ p := h1
      _ = U.sg (D.κ j) (D.b k) ^ p * ∑ α, (∏ j', uR hv D j' y ^ (α j').val) * bR hv D j α := by
          rw [h2]
      _ = ∑ α, (∏ j', uR hv D j' y ^ (α j').val) * (U.sg (U.φ (D.κ j)) (D.b k) * bR hv D j α) := by
          rw [D.frobChar, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α _ => by ring
  exact congrFun (mulVec_inj hv hp1 D key) α

theorem bR_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : bR hv D j (e1 l) = 0 := by
  obtain ⟨j'', hj''⟩ : ∃ j'', D.κ j'' = U.φ (D.κ j) := by
    have h := D.card_phi (D.κ j)
    have hpos : 0 < (Finset.univ.filter fun j' => D.κ j' = D.κ j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    rw [← h] at hpos
    obtain ⟨j'', hj''⟩ := Finset.card_pos.mp hpos
    exact ⟨j'', (Finset.mem_filter.mp hj'').2⟩
  obtain ⟨k, hk⟩ := D.sep l j'' (by rw [hj'']; exact hl)
  have he := bR_eig hv hp1 D j k (e1 l)
  rw [prod_pow_unitVector_val, ← hj''] at he
  have h0 : (U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k)) * bR hv D j (e1 l) = 0 := by
    rw [sub_mul, he, sub_self]
  have hne : U.sg (D.κ l) (D.b k) - U.sg (D.κ j'') (D.b k) ≠ 0 := by
    intro h0'
    rw [h0', map_zero, map_zero] at hk
    exact zero_ne_one hk
  have h2 := congrArg (algebraMap R C) h0
  rw [map_mul, map_zero] at h2
  have h3 : algebraMap R C (bR hv D j (e1 l)) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) hne
    · exact h
  exact hv.hom_inj (h3.trans (map_zero _).symm)

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

section Res

variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]

def Lk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  D.Λ.map (IsLocalRing.residue R)

def Mk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  (Lk D).map (fun a => a ^ p) * (Lk D)⁻¹

theorem Lk_det (D : Lifts H U X) : IsUnit (Lk D).det := by
  unfold Lk
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact D.Λ_det.map _

theorem lam_p (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    lam (Lk D) j y ^ p = ∑ l, Mk D j l * lam (Lk D) l y := by
  have hinv : (Lk D)⁻¹ * Lk D = 1 := Matrix.nonsing_inv_mul _ (Lk_det D)
  have hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y := by
    intro i
    simp only [xc]
    rw [← map_pow, ZMod.pow_card]
  have hR : ∑ l, Mk D j l * lam (Lk D) l y =
      ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j := by
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, lam]
  rw [hR]
  unfold Mk
  rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  simp only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  simp only [mul_pow, hxc]

theorem formMonomial_unitVector (D : Lifts H U X) (l : Ix g) (y : Nb p g) :
    monF (Lk D) (e1 l) y = lam (Lk D) l y := by
  simp only [monF, e1]
  rw [Finset.prod_eq_single l]
  · simp [ZMod.val_one]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem MuR_map (hv : v.Integers R) (D : Lifts H U X) :
    (MuR hv D).map (IsLocalRing.residue R) = Matrix.of fun (y α : Nb p g) => monF (Lk D) α y := by
  ext y α
  simp [MuR, monF, Lk, residue_uR hv]

theorem res_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) : IsLocalRing.residue R (bR hv D j (e1 l)) = Mk D j l := by
  classical
  have hMu := MuR_mulVec_bR hv hp1 D j
  have hdet : IsUnit ((MuR hv D).map (IsLocalRing.residue R)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_det_MuR hv hp1 D).map _
  let c : Nb p g → IsLocalRing.ResidueField R := fun α => ∑ l', if α = e1 l' then Mk D j l' else 0
  have hvecres : ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ
      (fun α => IsLocalRing.residue R (bR hv D j α)) = ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ c := by
    funext y
    have h1 : ((MuR hv D).map (IsLocalRing.residue R) *ᵥ fun α => IsLocalRing.residue R (bR hv D j α)) y =
        IsLocalRing.residue R (hvec hv D j y) := by
      rw [← hMu, RingHom.map_mulVec]
      rfl
    rw [h1, hvec, map_pow, residue_uR hv]
    change lam (Lk D) j y ^ p = _
    rw [lam_p, MuR_map hv D]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, c, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, formMonomial_unitVector]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hinv := Matrix.nonsing_inv_mul _ hdet
  have hinj : (fun α => IsLocalRing.residue R (bR hv D j α)) = c := by
    calc (fun α => IsLocalRing.residue R (bR hv D j α))
        = (((MuR hv D).map (IsLocalRing.residue R))⁻¹ * (MuR hv D).map (IsLocalRing.residue R)) *ᵥ
            (fun α => IsLocalRing.residue R (bR hv D j α)) := by rw [hinv, Matrix.one_mulVec]
      _ = c := by rw [← Matrix.mulVec_mulVec, hvecres, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hc : IsLocalRing.residue R (bR hv D j (e1 l)) = c (e1 l) := congrFun hinj (e1 l)
  rw [hc]
  simp only [c]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrFun h l
    simp [e1, Pi.single_apply, Ne.symm hb] at h2
  · simp

theorem Mk_det (D : Lifts H U X) : (Mk D).det ≠ 0 := by
  have h0 := (Lk_det D).ne_zero
  have hfrob : (Lk D).map (fun a => a ^ p) =
      (frobenius (IsLocalRing.ResidueField R) p).mapMatrix (Lk D) := by
    ext a b
    simp [frobenius_def]
  have hdet : ((Lk D).map (fun a => a ^ p)).det = (Lk D).det ^ p := by
    rw [hfrob, ← RingHom.map_det, frobenius_def]
  unfold Mk
  rw [Matrix.det_mul, hdet, Matrix.det_nonsing_inv]
  exact mul_ne_zero (pow_ne_zero _ h0) (by simpa [Ring.inverse_eq_inv] using h0)

theorem Mk_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : Mk D j l = 0 := by
  rw [← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]

theorem block_det_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let W : Ix g → IsLocalRing.ResidueField R := fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0
  apply Mk_det D
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨W, ?_, ?_⟩
  · intro hW
    apply hw0
    funext j
    have h1 := congrFun hW j.1
    simpa [W, j.2] using h1
  · funext l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hl : D.κ l = U.φ i
    · have h1 := congrFun hw (e.symm ⟨l, hl⟩)
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply,
        Pi.zero_apply] at h1
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]
      have h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [W, j.2]
      have h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l :=
        Finset.sum_congr rfl fun j _ => by simp [W, j.2]
      rw [h2, h3, add_zero]
      exact h1
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : D.κ j = i
      · rw [Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]
      · simp [W, hj]

end Res

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix ReciprocityTheory.PGsh.Up.UnitVectorPowers

theorem frobeniusBlock : FrobeniusBlockStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp _ hS H U X D
  have hv := hS.integers
  have hp1 := hS.p_lt
  haveI := isLocal_of_integers hv
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    have h0 := residue_p hv hp1
    first
      | exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0
      | exact CharP.of_prime_eq_zero Fact.out h0
      | exact (charP_iff_prime_eq_zero Fact.out).mpr h0
  refine ⟨fun j l hl => ?_, fun i e => ?_⟩
  · rw [linX_xp hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero, zero_mul]
  ·
    have hM : (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e l).1) =
        Matrix.of fun j l : {j // D.κ j = i} =>
          algebraMap R C (bR hv D j.1 (e1 (e l).1)) *
            (algebraMap R C (D.ε j.1) ^ p / algebraMap R C (D.ε (e l).1)) := by
      ext j l
      simp only [Matrix.of_apply]
      exact linX_xp hv hp1 D j.1 (e l).1
    have hs := Det2.v_det_scaled v
      (Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1)))
      (fun j => algebraMap R C (D.ε j.1) ^ p) (fun l => algebraMap R C (D.ε (e l).1))
    simp only [Matrix.of_apply] at hs

    have hcB : (Matrix.of fun j l : {j // D.κ j = i} =>
        algebraMap R C (bR hv D j.1 (e1 (e l).1))).det =
        algebraMap R C (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      rw [RingHom.map_det]
      first
        | rfl
        | (congr 1; ext j l; simp [RingHom.mapMatrix_apply])
    have hres : IsLocalRing.residue R
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det =
        (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det := by
      rw [RingHom.map_det]
      congr 1
      ext j l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact res_bR hv hp1 D _ _
    have hunit : IsUnit
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      by_contra h
      apply block_det_ne hv hp1 D i e
      rw [← hres, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have h1 := hv.one_of_isUnit hunit
    have hy : ∏ j : {j // D.κ j = i}, v (algebraMap R C (D.ε j.1) ^ p) = X i ^ p := by
      rw [← D.ε_prod i, ← Finset.prod_pow]
      simp only [map_pow]
      exact (Finset.prod_subtype _ (fun j => by simp)
        (fun j => v (algebraMap R C (D.ε j)) ^ p)).symm
    have hz : ∏ k : {j // D.κ j = i}, v (algebraMap R C (D.ε (e k).1)) = X (U.φ i) :=
      (Equiv.prod_comp e (fun l : {l // D.κ l = U.φ i} => v (algebraMap R C (D.ε l.1)))).trans
        ((Finset.prod_subtype _ (fun l => by simp)
          (fun l => v (algebraMap R C (D.ε l)))).symm.trans (D.ε_prod (U.φ i)))
    rw [hM, hs, hcB, h1, hy, hz, one_mul]

end ReciprocityTheory.PGsh.Up

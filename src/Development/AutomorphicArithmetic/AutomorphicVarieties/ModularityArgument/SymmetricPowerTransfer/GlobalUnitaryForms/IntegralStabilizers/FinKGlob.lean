module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import GroundTheory.GlobalFields.Adele.Approximation

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKLoc
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open Matrix Loc

variable {K K' : Type} [Field K] [Field K'] {Δ : K}

def qm (a b : Lsq K Δ) : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := !![a, b; -star b, star a]

def Shape (m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : Prop := m 1 1 = star (m 0 0) ∧ m 1 0 = -star (m 0 1)

theorem shape_qm (a b : Lsq K Δ) : Shape (qm a b) := ⟨rfl, rfl⟩

theorem Shape.eq {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) : m = qm (m 0 0) (m 0 1) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm, h.1, h.2]

theorem mem_DX (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ Shape (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
  change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = MulAut.conj (wJ Δ)⁻¹ g ↔ _
  rw [Units.ext_iff]
  simp [MulAut.conj_apply, wJ, Matrix.mul_apply, Fin.sum_univ_two, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Shape, starRingEnd_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, -⟩
    exact ⟨h1.symm, by rw [h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1.symm, by rw [h2, neg_neg]⟩, by rw [h2, star_neg, star_star], by rw [h1, star_star]⟩

theorem shape_mt (g : DX Δ) : Shape (mt g) := (mem_DX _).1 g.2

theorem lmap_star (f : K →+* K') (x : Lsq K Δ) : lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

theorem lmap_inj (f : K →+* K') : Function.Injective (lmap f Δ) := fun x y h => by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  exact QuadraticAlgebra.ext (f.injective h1) (f.injective h2)

theorem qm_map (f : K →+* K') (a b : Lsq K Δ) : (qm a b).map (lmap f Δ) = qm (lmap f Δ a) (lmap f Δ b) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm, lmap_star]

theorem shape_of_map (f : K →+* K') {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape (m.map (lmap f Δ))) : Shape m := by
  obtain ⟨h1, h2⟩ := h
  simp only [Matrix.map_apply, ← lmap_star, ← map_neg] at h1 h2
  exact ⟨lmap_inj f h1, lmap_inj f h2⟩

theorem det_qm (a b : Lsq K Δ) :
    (qm a b).det = algebraMap K (Lsq K Δ) (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2) := by
  rw [Matrix.det_fin_two]
  refine QuadraticAlgebra.ext ?_ ?_ <;> simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im] <;> simp [qm, pow_two] <;> ring

variable (O : Type) [CommRing O] [Algebra O K]

theorem int_star {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let φ : Lsq K Δ →ₐ[O] Lsq K Δ :=
    { starRingEnd (Lsq K Δ) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
        refine QuadraticAlgebra.ext ?_ ?_ <;> simp [starRingEnd_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] }
  exact h.map φ

variable (Δ) in
def RL : Subring (Matrix (Fin 2) (Fin 2) (Lsq K Δ)) where
  carrier := {m | Shape m ∧ ∀ i j, IsIntegral O (m i j)}
  mul_mem' := by
    rintro a b ⟨⟨h1, h2⟩, ha⟩ ⟨⟨h3, h4⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, fun i j => ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact ((ha _ _).mul (hb _ _)).add ((ha _ _).mul (hb _ _))
  one_mem' := ⟨⟨by simp, by simp⟩, fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_one, isIntegral_zero]⟩
  add_mem' := by
    rintro a b ⟨⟨h1, h2⟩, ha⟩ ⟨⟨h3, h4⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, fun i j => (ha i j).add (hb i j)⟩
    · simp [h1, h3]
    · simp [h2, h4]; ring
  zero_mem' := ⟨⟨by simp, by simp⟩, fun i j => isIntegral_zero⟩
  neg_mem' := by
    rintro a ⟨⟨h1, h2⟩, ha⟩
    exact ⟨⟨by simp [h1], by simp [h2]⟩, fun i j => (ha i j).neg⟩

theorem qm_mem {a b : Lsq K Δ} (ha : IsIntegral O a) (hb : IsIntegral O b) : qm a b ∈ RL Δ O := by
  refine ⟨shape_qm a b, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [qm]
  all_goals first
    | assumption
    | exact int_star O hb
    | exact int_star O ha
    | simpa using (int_star O hb).neg
    | simpa using (int_star O ha).neg

theorem mem_KD (g : DX Δ) : g ∈ KD Δ O ↔ mt g ∈ RL Δ O ∧ mt g⁻¹ ∈ RL Δ O := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    have e1 : mt g = (u : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map Subtype.val := by
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hu]; rfl
    have e2 : mt g⁻¹ = ((u⁻¹ : GL (Fin 2) (integralClosure O (Lsq K Δ))) : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))).map Subtype.val := by
      show (((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [Subgroup.coe_inv, ← hu, ← map_inv]; rfl
    refine ⟨⟨shape_mt g, fun i j => ?_⟩, ⟨shape_mt g⁻¹, fun i j => ?_⟩⟩
    · rw [e1]; exact ((u : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) i j).2
    · rw [e2]; exact (((u⁻¹ : GL (Fin 2) (integralClosure O (Lsq K Δ))) : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) i j).2
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    let f := (integralClosure O (Lsq K Δ)).val.toRingHom
    let A : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨mt g i j, h1 i j⟩
    let B : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨mt g⁻¹ i j, h2 i j⟩
    have hA : A.map f = mt g := rfl
    have hB : B.map f = mt g⁻¹ := rfl
    have inj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) => M.map f) :=
      fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    have hAB : A * B = 1 := inj (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f)]
      show mt (g * g⁻¹) = 1
      rw [mul_inv_cancel]; rfl)
    have hBA : B * A = 1 := inj (by
      simp only [Matrix.map_mul, hA, hB, Matrix.map_one f (map_zero f) (map_one f)]
      show mt (g⁻¹ * g) = 1
      rw [inv_mul_cancel]; rfl)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem mt_mul (g h : DX Δ) : mt (g * h) = mt g * mt h := rfl

theorem conj_mem {u : DX Δ} (hu : u ∈ ZD Δ ⊔ KD Δ O) {r : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (hr : r ∈ RL Δ O) :
    mt u * r * mt u⁻¹ ∈ RL Δ O := by
  have mt1 : mt (1 : DX Δ) = 1 := rfl
  have base : ∀ w : DX Δ, w ∈ ZD Δ ∨ w ∈ KD Δ O → ∀ s ∈ RL Δ O, mt w * s * mt w⁻¹ ∈ RL Δ O := by
    rintro w (hw | hw) s hs
    · rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hw
      obtain ⟨t, ht⟩ := hw
      have hc : Commute (mt w) s := by
        show Commute ((w : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s
        rw [← ht]
        exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) s
      rw [hc.eq, mul_assoc, ← mt_mul, mul_inv_cancel, mt1, mul_one]
      exact hs
    · obtain ⟨h1, h2⟩ := (mem_KD O w).1 hw
      exact (RL Δ O).mul_mem ((RL Δ O).mul_mem h1 hs) h2
  rw [Subgroup.sup_eq_closure] at hu
  refine (Subgroup.closure_induction
    (p := fun v _ => (∀ s ∈ RL Δ O, mt v * s * mt v⁻¹ ∈ RL Δ O) ∧ (∀ s ∈ RL Δ O, mt v⁻¹ * s * mt v ∈ RL Δ O))
    ?_ ?_ ?_ ?_ hu).1 r hr
  · intro x hx
    refine ⟨base x hx, fun s hs => ?_⟩
    have hx' : x⁻¹ ∈ ZD Δ ∨ x⁻¹ ∈ KD Δ O := hx.imp (fun h => inv_mem h) (fun h => inv_mem h)
    simpa using base x⁻¹ hx' s hs
  · refine ⟨fun s hs => ?_, fun s hs => ?_⟩ <;> simpa [mt1] using hs
  · rintro x y - - ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have e : mt (x * y) * s * mt (x * y)⁻¹ = mt x * (mt y * s * mt y⁻¹) * mt x⁻¹ := by
        simp only [_root_.mul_inv_rev, mt_mul, mul_assoc]
      rw [e]; exact hx1 _ (hy1 s hs)
    · have e : mt (x * y)⁻¹ * s * mt (x * y) = mt y⁻¹ * (mt x⁻¹ * s * mt x) * mt y := by
        simp only [_root_.mul_inv_rev, mt_mul, mul_assoc]
      rw [e]; exact hy2 _ (hx2 s hs)
  · rintro x - ⟨hx1, hx2⟩
    exact ⟨hx2, by simpa using hx1⟩

theorem int_alg {x : K} : IsIntegral O (algebraMap K (Lsq K Δ) x) ↔ IsIntegral O x := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom O K (Lsq K Δ)) := by
    intro u v huv
    have := congrArg QuadraticAlgebra.re huv
    simpa using this
  exact isIntegral_algHom_iff _ hinj

theorem int_re {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (2 * x.re) := by
  have e : x + star x = algebraMap K (Lsq K Δ) (2 * x.re) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;> ring
  rw [← int_alg O, ← e]
  exact h.add (int_star O h)

theorem int_om {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) : IsIntegral O (⟨0, c⟩ : Lsq K Δ) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  have e : (⟨0, c⟩ : Lsq K Δ) ^ 2 = algebraMap K (Lsq K Δ) (c * ((c : K) * Δ)) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [pow_two] <;> ring
  rw [e, int_alg O]
  exact (isIntegral_natCast c).mul hc

theorem int_im {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (2 * c * Δ * x.im) := by
  have e : (⟨0, c⟩ : Lsq K Δ) * (x - star x) = algebraMap K (Lsq K Δ) (2 * c * Δ * x.im) := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;> ring
  rw [← int_alg O, ← e]
  exact (int_om O hc).mul (h.sub (int_star O h))

theorem int_mk {c : ℕ} (hc : IsIntegral O ((c : K) * Δ)) {r s : K} (hr : IsIntegral O r) (hs : IsIntegral O s) :
    IsIntegral O (⟨r, c * s⟩ : Lsq K Δ) := by
  have e : (⟨r, c * s⟩ : Lsq K Δ) = algebraMap K (Lsq K Δ) r + (⟨0, c⟩ : Lsq K Δ) * algebraMap K (Lsq K Δ) s := by
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  rw [e]
  exact ((int_alg O).2 hr).add ((int_om O hc).mul ((int_alg O).2 hs))

theorem mem_ZD [CharZero K] (hΔ : Δ ≠ 0) {c : K} (hc : c ≠ 0) (g : DX Δ) (h1 : mt g * qm ⟨0, c⟩ 0 = qm ⟨0, c⟩ 0 * mt g)
    (h2 : mt g * qm 0 1 = qm 0 1 * mt g) : g ∈ ZD Δ := by
  have hs := shape_mt g
  have a01 := congrFun (congrFun h1 0) 1
  have b00 := congrFun (congrFun h2 0) 0
  have b01 := congrFun (congrFun h2 0) 1
  simp [qm, Matrix.mul_apply, Fin.sum_univ_two, QuadraticAlgebra.ext_iff] at a01 b00 b01
  have two : (2 : K) ≠ 0 := two_ne_zero
  have q01 : mt g 0 1 = 0 := by
    refine QuadraticAlgebra.ext ?_ ?_
    · have e : (2 * c) * (mt g 0 1).re = 0 := by linear_combination -a01.2
      simpa [two, hc] using e
    · have e : (2 * Δ * c) * (mt g 0 1).im = 0 := by linear_combination -a01.1
      simpa [two, hc, hΔ] using e
  have r10 : mt g 1 0 = 0 := by
    refine QuadraticAlgebra.ext ?_ ?_
    · rw [← b00.1]; simp [q01]
    · rw [← b00.2]; simp [q01]
  have s11 : mt g 1 1 = mt g 0 0 := (QuadraticAlgebra.ext b01.1 b01.2).symm
  have pim : (mt g 0 0).im = 0 := by
    have e := congrArg QuadraticAlgebra.im hs.1
    rw [s11, QuadraticAlgebra.im_star] at e
    have e2 : 2 * (mt g 0 0).im = 0 := by linear_combination e
    simpa [two] using e2
  have hp : mt g 0 0 = algebraMap K (Lsq K Δ) (mt g 0 0).re :=
    QuadraticAlgebra.ext (by simp) (by simp [pim])
  have hre : (mt g 0 0).re ≠ 0 := by
    intro h0
    have e := congrFun (congrFun (show mt g * mt g⁻¹ = 1 by rw [← mt_mul, mul_inv_cancel]; rfl) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hp, h0, q01] at e
    have h3 := congrArg QuadraticAlgebra.re e
    have h11 : (1 : Lsq K Δ).re = 1 := rfl
    simp [h11] at h3
  rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine ⟨Units.mk0 _ hre, Units.ext (Matrix.ext fun i j => ?_)⟩
  fin_cases i <;> fin_cases j <;> simp
  · exact hp.symm
  · exact q01.symm
  · exact r10.symm
  · exact (s11.trans hp).symm

theorem exists_DX {a b : Lsq K Δ} (h : a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2 ≠ 0) : ∃ g : DX Δ, mt g = qm a b := by
  have hu : IsUnit (qm a b).det := by
    rw [det_qm]
    exact ((Units.mk0 _ h).map (algebraMap K (Lsq K Δ)).toMonoidHom).isUnit
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' (qm a b) hu, (mem_DX _).2 (shape_qm a b)⟩, rfl⟩

theorem shape_nat (n : ℕ) {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) :
    Shape ((n : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * m) := by
  obtain ⟨h1, h2⟩ := h
  rw [← Matrix.diagonal_natCast']
  constructor <;> simp [Matrix.diagonal_mul, h1, h2, mul_comm]

theorem den_mat {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral O ((c : K) * Δ)) (hd : ∀ x : K, ∃ n : ℕ, n ≠ 0 ∧ IsIntegral O ((n : K) * x))
    {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : Shape m) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * m ∈ RL Δ O := by
  have one : ∀ x : Lsq K Δ, ∃ n : ℕ, n ≠ 0 ∧ IsIntegral O ((n : Lsq K Δ) * x) := by
    intro x
    obtain ⟨n1, hn1, h1⟩ := hd x.re
    obtain ⟨n2, hn2, h2⟩ := hd (x.im / c)
    refine ⟨n1 * n2, mul_ne_zero hn1 hn2, ?_⟩
    have e : ((n1 * n2 : ℕ) : Lsq K Δ) * x = ⟨n2 * (n1 * x.re), c * (n1 * (n2 * (x.im / c)))⟩ := by
      refine QuadraticAlgebra.ext ?_ ?_
      · simp; ring
      · simp; field_simp
    rw [e]
    exact int_mk O hc ((isIntegral_natCast n2).mul h1) ((isIntegral_natCast n1).mul h2)
  obtain ⟨na, hna, ha⟩ := one (m 0 0)
  obtain ⟨nb, hnb, hb⟩ := one (m 0 1)
  refine ⟨nb * na, mul_ne_zero hnb hna, shape_nat (nb * na) h, fun i j => ?_⟩
  have hA : IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 0 0) := by
    rw [Nat.cast_mul, mul_assoc]; exact (isIntegral_natCast nb).mul ha
  have hB : IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 0 1) := by
    rw [Nat.cast_mul, mul_comm (nb : Lsq K Δ), mul_assoc]; exact (isIntegral_natCast na).mul hb
  have st : ∀ x : Lsq K Δ, ((nb * na : ℕ) : Lsq K Δ) * star x = star (((nb * na : ℕ) : Lsq K Δ) * x) := by
    intro x; rw [star_mul, star_natCast, mul_comm]
  rw [← Matrix.diagonal_natCast', Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · exact hA
  · exact hB
  · show IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 1 0)
    rw [h.2, mul_neg, st]; exact (int_star O hB).neg
  · show IsIntegral O (((nb * na : ℕ) : Lsq K Δ) * m 1 1)
    rw [h.1, st]; exact int_star O hA

end UpperTheory.V.Z.Sym.Glob.FK
end
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open NumberField IsDedekindDomain Matrix Loc

theorem lmap_re {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).re = f x.re := rfl

theorem lmap_im {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).im = f x.im := rfl

variable {F : Type} [Field F] [NumberField F]

theorem int_iff (v : Pl F) (x : Kv v) : IsIntegral (Ov v) x ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem int_glob (x : F) : IsIntegral ℤ x ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v x) := by
  simp only [int_iff]
  refine ⟨fun h v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨x, h⟩, fun h => ?_⟩
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v =>
    (GroundTheory.Global.coe_mem_adicCompletionIntegers_iff v x).1 (h v)
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

theorem den_glob (x : F) : ∃ c : ℕ, c ≠ 0 ∧ IsIntegral ℤ ((c : F) * x) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem approx_F (a : ∀ v : Pl F, Kv v) {e f : F} (he : e ≠ 0) (hf : f ≠ 0) (ha : ∀ v, IsIntegral (Ov v) (cv v e * a v)) :
    ∃ x : F, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = cv v x + cv v f * r := by
  let b : FiniteAdeleRing (𝓞 F) F := ⟨fun v => cv v e * a v, Filter.Eventually.of_forall fun v => (int_iff v _).1 (ha v)⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e * f)⁻¹ * b)
  refine ⟨f * k, fun v => ⟨cv v (e * f)⁻¹ * (cv v e * a v) - cv v k, (int_iff v _).2 (hk v), ?_⟩⟩
  have h1 : cv v e ≠ 0 := (map_ne_zero _).2 he
  have h2 : cv v f ≠ 0 := (map_ne_zero _).2 hf
  rw [map_inv₀, map_mul, map_mul]
  field_simp
  ring

theorem den_loc (v : Pl F) (x : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * x) := by
  have hU : IsOpen {w : Kv v | x - w ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (Kv v)).preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_mem_open hU ⟨x, by simp⟩
  obtain ⟨n, hn, h⟩ := den_glob z
  refine ⟨n, hn, ?_⟩
  have h1 := (int_glob _).1 h v
  rw [map_mul, map_natCast] at h1
  have e : (n : Kv v) * x = n * cv v z + n * (x - cv v z) := by ring
  rw [e]
  exact h1.add ((isIntegral_natCast (R := Ov v) (B := Kv v) n).mul ((int_iff v _).2 hz))

variable {Δ : F}

theorem int_cD {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) (v : Pl F) : IsIntegral (Ov v) ((c : Kv v) * cv v Δ) := by
  have h1 := (int_glob _).1 hc v
  rwa [map_mul, map_natCast] at h1

theorem approx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : Lsq F Δ, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = lmap (cv v) Δ x + n • r := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : F) ≠ 0 := Nat.cast_ne_zero.2 hc0
  obtain ⟨x, hx⟩ := approx_F (fun v => (a v).re) (e := 2) two_ne_zero hn' fun v => by
    rw [map_ofNat]; exact int_re _ (ha v)
  obtain ⟨y, hy⟩ := approx_F (fun v => (a v).im) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (mul_ne_zero hn' hc') fun v => by
    rw [map_mul, map_mul, map_ofNat, map_natCast]; exact int_im _ (int_cD hc v) (ha v)
  refine ⟨⟨x, y⟩, fun v => ?_⟩
  obtain ⟨r, hr, e1⟩ := hx v
  obtain ⟨s, hs, e2⟩ := hy v
  refine ⟨_, int_mk _ (int_cD hc v) hr hs, ?_⟩
  ext : 1
  · rw [e1]; simp [lmap]
  · rw [e2]; simp [lmap, mul_assoc]

variable (Δ)

abbrev MM : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

def RR : Subring (MM Δ) := ⨅ v, (RL (cv v Δ) (Ov v)).comap (Pi.evalRingHom _ v)

def jj : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* MM Δ := Pi.ringHom fun v => (lmap (cv v) Δ).mapMatrix

variable {Δ}

theorem mem_RR {m : MM Δ} : m ∈ RR Δ ↔ ∀ v, m v ∈ RL (cv v Δ) (Ov v) := Subring.mem_iInf

theorem jj_apply (y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) (v : Pl F) : jj Δ y v = y.map (lmap (cv v) Δ) := rfl

theorem pl_ne : Nonempty (Pl F) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩⟩

theorem lam_shape {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) : Shape y := by
  obtain ⟨v⟩ := pl_ne (F := F)
  exact shape_of_map (cv v) (mem_RR.1 h v).1

theorem lam_int {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) (i j : Fin 2) :
    IsIntegral ℤ (2 * (y i j).re) ∧ IsIntegral ℤ (2 * c * Δ * (y i j).im) := by
  have h1 : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ (y i j)) := fun v => by
    have h2 := (mem_RR.1 (Subring.mem_comap.1 h) v).2 i j
    rwa [jj_apply, Matrix.map_apply] at h2
  refine ⟨(int_glob _).2 fun v => ?_, (int_glob _).2 fun v => ?_⟩
  · have h2 := int_re _ (h1 v)
    rw [lmap_re] at h2
    rwa [map_mul, map_ofNat]
  · have h2 := int_im _ (int_cD hc v) (h1 v)
    rw [lmap_im] at h2
    rwa [map_mul, map_mul, map_mul, map_ofNat, map_natCast]

theorem lam_fg (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RR Δ).comap (jj Δ)) := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  let ψ : (RR Δ).comap (jj Δ) →+ (Fin 2 → Fin 2 → 𝓞 F × 𝓞 F) := AddMonoidHom.mk'
    (fun y i j => (⟨_, (lam_int hc y.2 i j).1⟩, ⟨_, (lam_int hc y.2 i j).2⟩)) fun x y => by
      funext i j
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact mul_add _ _ _
      · exact mul_add _ _ _
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Matrix.ext fun i j => ?_)
  have h1 := congrFun (congrFun h i) j
  exact QuadraticAlgebra.ext (mul_left_cancel₀ two_ne_zero (congrArg Subtype.val (congrArg Prod.fst h1)))
    (mul_left_cancel₀ (by simp [hc0, hΔ]) (congrArg Subtype.val (congrArg Prod.snd h1)))

theorem approx_R (hΔ : Δ ≠ 0) : ∀ m ∈ RR Δ, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ (RR Δ).comap (jj Δ), ∃ r ∈ RR Δ, m = jj Δ x + (n : MM Δ) * r := by
  intro m hm n hn
  obtain ⟨a, ha⟩ := approx_L hΔ (fun v => m v 0 0) (fun v => (mem_RR.1 hm v).2 0 0) hn
  obtain ⟨b, hb⟩ := approx_L hΔ (fun v => m v 0 1) (fun v => (mem_RR.1 hm v).2 0 1) hn
  choose r hr ha using ha
  choose s hs hb using hb
  have h1 : (fun v => qm (r v) (s v) : MM Δ) ∈ RR Δ := mem_RR.2 fun v => qm_mem _ (hr v) (hs v)
  have e : m = jj Δ (qm a b) + (n : MM Δ) * fun v => qm (r v) (s v) := by
    funext v
    rw [← nsmul_eq_mul, Pi.add_apply, Pi.smul_apply, jj_apply, qm_map, (mem_RR.1 hm v).1.eq, ha v, hb v]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [qm, add_comm]
  refine ⟨qm a b, ?_, _, h1, e⟩
  rw [Subring.mem_comap, ← sub_eq_of_eq_add e]
  exact sub_mem hm (mul_mem (natCast_mem _ n) h1)

theorem form_pos (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (σ : F →+* ℝ) (a b : Lsq F Δ) :
    let d := σ (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2)
    σ a.re ^ 2 ≤ d ∧ σ b.re ^ 2 ≤ d ∧ -σ Δ * σ a.im ^ 2 ≤ d ∧ -σ Δ * σ b.im ^ 2 ≤ d := by
  have h := hneg σ
  have h1 : 0 ≤ -σ Δ * σ a.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -σ Δ * σ b.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  simp only [map_add (f := _), map_sub, map_mul, map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (σ a.re), sq_nonneg (σ b.re)]

theorem real_emb [IsTotallyReal F] (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, (σ x : ℂ) = φ x :=
  ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, fun x => ComplexEmbedding.IsReal.coe_embedding_apply _ x⟩

theorem unit_of_shape [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : Shape y) (h0 : y ≠ 0) :
    ∃ g : DX Δ, mt g = y := by
  rw [h.eq]
  refine exists_DX fun hd => h0 ?_
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := real_emb φ
  have := form_pos hneg σ (y 0 0) (y 0 1)
  rw [hd, map_zero] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  have hσ := hneg σ
  have z : ∀ x : F, σ x ^ 2 ≤ 0 → x = 0 := fun x hx => (map_eq_zero σ).1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hx (sq_nonneg _)))
  have a0 : y 0 0 = 0 := QuadraticAlgebra.ext (z _ h1) (z _ (by nlinarith [sq_nonneg (σ (y 0 0).im)]))
  have b0 : y 0 1 = 0 := QuadraticAlgebra.ext (z _ h2) (z _ (by nlinarith [sq_nonneg (σ (y 0 1).im)]))
  rw [h.eq, a0, b0]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm]

theorem box_fin [IsTotallyReal F] {e : F} (he : e ≠ 0) (d : F) :
    {x : F | IsIntegral ℤ (e * x) ∧ ∀ σ : F →+* ℝ, σ (e * x) ^ 2 ≤ σ d}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, (‖φ d‖ + 1))
  refine (h.preimage (f := fun x : F => e * x) (mul_right_injective₀ he).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ d‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ φ))
  obtain ⟨σ, hσ⟩ := real_emb φ
  have h1 := hA σ
  rw [← hσ, ← hσ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [← sq_abs] at h1
  nlinarith [le_abs_self (σ d), abs_nonneg (σ (e * x)), sq_nonneg (|σ (e * x)| - 1), abs_nonneg (σ d)]

theorem det_fin [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (hΔ : Δ ≠ 0) (d : Lsq F Δ) :
    {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ) | y ∈ (RR Δ).comap (jj Δ) ∧ y.det = d}.Finite := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have h1 := box_fin (F := F) (e := 2) two_ne_zero (4 * d.re)
  have h2 := box_fin (F := F) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (-(4 * c ^ 2 * Δ) * d.re)
  refine ((((h1.prod h2).prod (h1.prod h2)).image fun p => qm ⟨p.1.1, p.1.2⟩ ⟨p.2.1, p.2.2⟩)).subset ?_
  rintro y ⟨hy, hd⟩
  have hs := lam_shape hy
  refine ⟨(((y 0 0).re, (y 0 0).im), ((y 0 1).re, (y 0 1).im)), ?_, hs.eq.symm⟩
  rw [hs.eq, det_qm] at hd
  have hd' : d.re = (y 0 0).re ^ 2 - Δ * (y 0 0).im ^ 2 + (y 0 1).re ^ 2 - Δ * (y 0 1).im ^ 2 := by rw [← hd]; rfl
  have k1 : ∀ (σ : F →+* ℝ) (x : F), σ x ^ 2 ≤ σ d.re → σ (2 * x) ^ 2 ≤ σ (4 * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat]; nlinarith
  have k2 : ∀ (σ : F →+* ℝ) (x : F), -σ Δ * σ x ^ 2 ≤ σ d.re → σ (2 * c * Δ * x) ^ 2 ≤ σ (-(4 * c ^ 2 * Δ) * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat, map_neg, map_pow, map_natCast]
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * (c : ℝ) ^ 2 * -σ Δ from mul_nonneg (by positivity) (by linarith [hneg σ]))
    nlinarith
  have f := fun σ => form_pos hneg σ (y 0 0) (y 0 1)
  rw [← hd'] at f
  exact ⟨⟨⟨(lam_int hc hy 0 0).1, fun σ => k1 σ _ (f σ).1⟩, (lam_int hc hy 0 0).2, fun σ => k2 σ _ (f σ).2.2.1⟩,
    ⟨(lam_int hc hy 0 1).1, fun σ => k1 σ _ (f σ).2.1⟩, (lam_int hc hy 0 1).2, fun σ => k2 σ _ (f σ).2.2.2⟩

variable (Δ) in
def rho : DA Δ →* MM Δ where
  toFun g v := mt (g.1 v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem den_rho (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ (n : MM Δ) * rho Δ g ∈ RR Δ := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hT : {v : Pl F | g.1 v ∉ KD (cv v Δ) (Ov v)}.Finite := Filter.eventually_cofinite.1 g.2
  choose n hn0 hn using fun v : Pl F => den_mat (Ov v) (c := c)
    (by rw [← map_natCast (cv v)]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hc0)) (int_cD hc v) (den_loc v) (shape_mt (g.1 v))
  refine ⟨∏ v ∈ hT.toFinset, n v, Finset.prod_ne_zero_iff.2 fun v _ => hn0 v, mem_RR.2 fun v => ?_⟩
  rw [← nsmul_eq_mul, Pi.smul_apply]
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact nsmul_mem ((mem_KD _ _).1 hv).1 _
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hT.mem_toFinset.2 hv)
    rw [hk, mul_nsmul, nsmul_eq_mul (n v)]
    exact nsmul_mem (hn v) k

end UpperTheory.V.Z.Sym.Glob.FK

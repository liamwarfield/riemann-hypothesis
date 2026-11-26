module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmple
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfCls
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIsMonHomIdPow

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ZarhinStatementOfDualCubeQiR
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KLiftSqToBase
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.EightfoldProjection
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Points

variable {Y : Over S}

def mk8 (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) : Y ⟶ G4 (A ⊗ B) :=
  lift (lift (x 0) (z 0)) (lift (lift (x 1) (z 1)) (lift (lift (x 2) (z 2)) (lift (x 3) (z 3))))

omit [GrpObj A] [GrpObj B] in
theorem eightfold_projection (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) (i : Fin 4) :
    mk8 x z ≫ prj (A ⊗ B) i = lift (x i) (z i) := by
  fin_cases i <;> simp [mk8, prj]

omit [GrpObj A] [GrpObj B] in
theorem eightfold_fst (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) (i : Fin 4) :
    mk8 x z ≫ prj (A ⊗ B) i ≫ fst A B = x i := by
  rw [← Category.assoc, eightfold_projection]; simp

omit [GrpObj A] [GrpObj B] in
theorem eightfold_snd (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) (i : Fin 4) :
    mk8 x z ≫ prj (A ⊗ B) i ≫ snd A B = z i := by
  rw [← Category.assoc, eightfold_projection]; simp

omit [GrpObj A] [GrpObj B] in
theorem eightfold_fst_assoc (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) (i : Fin 4) {W : Over S} (f : A ⟶ W) :
    mk8 x z ≫ prj (A ⊗ B) i ≫ fst A B ≫ f = x i ≫ f := by
  rw [reassoc_of% (eightfold_fst x z i)]

omit [GrpObj A] [GrpObj B] in
theorem eightfold_snd_assoc (x : Fin 4 → (Y ⟶ A)) (z : Fin 4 → (Y ⟶ B)) (i : Fin 4) {W : Over S} (f : B ⟶ W) :
    mk8 x z ≫ prj (A ⊗ B) i ≫ snd A B ≫ f = z i ≫ f := by
  rw [reassoc_of% (eightfold_snd x z i)]


omit [GrpObj A] [GrpObj B] in
theorem ext8 {a b : Y ⟶ G4 (A ⊗ B)} (hx : ∀ i, a ≫ prj _ i ≫ fst A B = b ≫ prj _ i ≫ fst A B)
    (hz : ∀ i, a ≫ prj _ i ≫ snd A B = b ≫ prj _ i ≫ snd A B) : a = b := by
  have h : ∀ i, a ≫ prj (A ⊗ B) i = b ≫ prj (A ⊗ B) i := fun i =>
    CartesianMonoidalCategory.hom_ext _ _ (by simpa using hx i) (by simpa using hz i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [prj] at h0 h1 h2 h3
  refine CartesianMonoidalCategory.hom_ext _ _ h0
    (CartesianMonoidalCategory.hom_ext _ _ (by simpa using h1)
      (CartesianMonoidalCategory.hom_ext _ _ (by simpa using h2) (by simpa using h3)))

theorem kIsMonHom_prj (i : Fin 4) : IsMonHom (prj (A ⊗ B) i) := by
  fin_cases i <;> simp [prj] <;> infer_instance

theorem one_prj_fst (i : Fin 4) : (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj (A ⊗ B) i ≫ fst A B = 1 := by
  have := kIsMonHom_prj (A := A) (B := B) i
  rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]

theorem one_prj_snd (i : Fin 4) : (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj (A ⊗ B) i ≫ snd A B = 1 := by
  have := kIsMonHom_prj (A := A) (B := B) i
  rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]

end Points

section Hom

variable {T T' G H : Over S} [GrpObj G] [GrpObj H]

def postH (f : G ⟶ H) [IsMonHom f] : (T ⟶ G) →* (T ⟶ H) :=
  MonoidHom.mk' (· ≫ f) fun x y => MonObj.mul_comp x y f

def preH (U : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y

theorem comp_id_pow (x : T ⟶ G) (m : ℕ) : x ≫ 𝟙 G ^ m = x ^ m := by
  induction m with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end Hom

section Evc

variable {Y : Over S} {P : LB (A ⊗ B).left} [IsCommMonObj A] [IsCommMonObj B]

theorem kEvc_mul_left (hD : IsDual A B P) (a a' : Y ⟶ A) (b : Y ⟶ B) :
    evc hD.isLB (a * a') b = evc hD.isLB a b + evc hD.isLB a' b :=
  (isAdditive_iff hD.isLB).1 hD.additive Y a a' b

theorem kEvc_mul_right (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB a (b * b') = evc hD.isLB a b + evc hD.isLB a b' := by
  rw [← evc_swap hD.isLB hD'.isLB (b * b') a, ← evc_swap hD.isLB hD'.isLB b a,
    ← evc_swap hD.isLB hD'.isLB b' a]
  exact (isAdditive_iff hD'.isLB).1 hD'.additive Y b b' a

def evcR (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (a : Y ⟶ A) : (Y ⟶ B) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hD.isLB a b)) fun b b' => by
    simp [kEvc_mul_right hD hD', ofAdd_add]

def evcL (hD : IsDual A B P) (b : Y ⟶ B) : (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hD.isLB a b)) fun a a' => by
    simp [kEvc_mul_left hD, ofAdd_add]

theorem evc_right_pow_prod (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ)
    (c : Fin 4 → (Y ⟶ B)) (k : Fin 4 → ℤ) :
    evc hD.isLB a (b ^ n * ∏ j, c j ^ k j) = n • evc hD.isLB a b + ∑ j, k j • evc hD.isLB a (c j) := by
  have e : ∀ x, evc hD.isLB a x = Multiplicative.toAdd (evcR hD hD' a x) := fun _ => rfl
  rw [e, map_mul, map_pow, map_prod, toAdd_mul, toAdd_pow, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← e]

theorem evc_right_pow (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    evc hD.isLB a (b ^ n) = n • evc hD.isLB a b := by
  have e : ∀ x, evc hD.isLB a x = Multiplicative.toAdd (evcR hD hD' a x) := fun _ => rfl
  rw [e, map_pow, toAdd_pow, ← e]

theorem evc_left_prod_pow (hD : IsDual A B P) (c : Fin 4 → (Y ⟶ A)) (k : Fin 4 → ℤ) (d : Y ⟶ A) (n : ℕ)
    (b : Y ⟶ B) :
    evc hD.isLB ((∏ j, c j ^ k j) * d ^ n) b = ∑ j, k j • evc hD.isLB (c j) b + n • evc hD.isLB d b := by
  have e : ∀ x, evc hD.isLB x b = Multiplicative.toAdd (evcL hD b x) := fun _ => rfl
  rw [e, map_mul, map_pow, map_prod, toAdd_mul, toAdd_pow, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← e]

end Evc

section Slots

variable {Y : Over S} {P : LB (A ⊗ B).left}

theorem zcPair_positionA (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) (u : Y ⟶ G4 (A ⊗ B)) (x' : Y ⟶ A) (i : Fin 4) :
    zcPair hD.isLB l mu α u (mk8 (fun k => if k = i then x' else 1) (fun _ => 1)) =
      2 • evc hD.isLB (u ≫ prj _ i ≫ fst A B) (x' ≫ l) +
        ∑ j, α i j • evc hD.isLB x' (u ≫ prj _ j ≫ snd A B) := by
  have r1 : ∀ (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 := evc_one_right hD.isLB hD.zero
  have l1 : ∀ (b : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) b = 0 := IsAdditive.evc_one hD.isLB hD.additive
  have c1 : ∀ {W : Over S} [GrpObj W] (f : A ⟶ W) [IsMonHom f], (1 : Y ⟶ A) ≫ f = 1 := fun f => MonObj.one_comp f
  have c2 : ∀ {W : Over S} [GrpObj W] (f : B ⟶ W) [IsMonHom f], (1 : Y ⟶ B) ≫ f = 1 := fun f => MonObj.one_comp f
  have e : ∀ k : Fin 4, (if k = i then x' else (1 : Y ⟶ A)) ≫ l = if k = i then x' ≫ l else 1 := by
    intro k; split_ifs <;> simp [c1]
  simp only [zcPair, eightfold_fst, eightfold_snd, eightfold_fst_assoc, eightfold_snd_assoc, e, c2, r1, add_zero, smul_zero,
    Finset.sum_const_zero, apply_ite (evc hD.isLB _), l1]
  simp
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk, l1]) (by simp)]
  simp

theorem zcPair_positionB (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) (u : Y ⟶ G4 (A ⊗ B)) (z' : Y ⟶ B) (j : Fin 4) :
    zcPair hD.isLB l mu α u (mk8 (fun _ => 1) (fun k => if k = j then z' else 1)) =
      ∑ k, α k j • evc hD.isLB (u ≫ prj _ k ≫ fst A B) z' +
        2 • evc hD.isLB (u ≫ prj _ j ≫ snd A B ≫ mu) (z' ≫ mu ≫ l) := by
  have r1 : ∀ (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 := evc_one_right hD.isLB hD.zero
  have l1 : ∀ (b : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) b = 0 := IsAdditive.evc_one hD.isLB hD.additive
  have c1 : ∀ {W : Over S} [GrpObj W] (f : A ⟶ W) [IsMonHom f], (1 : Y ⟶ A) ≫ f = 1 := fun f => MonObj.one_comp f
  have c2 : ∀ {W : Over S} [GrpObj W] (f : B ⟶ W) [IsMonHom f], (1 : Y ⟶ B) ≫ f = 1 := fun f => MonObj.one_comp f
  have e : ∀ k : Fin 4, (if k = j then z' else (1 : Y ⟶ B)) ≫ mu ≫ l = if k = j then z' ≫ mu ≫ l else 1 := by
    intro k; split_ifs
    · rfl
    · rw [← Category.assoc, c2, c1]
  have e' : ∀ k : Fin 4, (if k = j then z' else (1 : Y ⟶ B)) ≫ mu = if k = j then z' ≫ mu else 1 := by
    intro k; split_ifs <;> simp [c2]
  simp only [zcPair, eightfold_fst, eightfold_snd, eightfold_fst_assoc, eightfold_snd_assoc, c1, r1, l1, add_zero, zero_add, smul_zero,
    Finset.sum_const_zero]
  rw [Finset.sum_comm]
  simp only [apply_ite (evc hD.isLB _), r1, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk, e, e', r1]) (by simp)]
    simp
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk, e, r1]) (by simp)]
    simp

end Slots


omit [GrpObj A] [GrpObj B] in
theorem zcPair_pull {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y Y' : Over S} (h : Y' ⟶ Y) (u u' : Y ⟶ G4 (A ⊗ B)) :
    pull h.left (zcPair hP l mu α u u') = zcPair hP l mu α (h ≫ u) (h ≫ u') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zcPair, map_add (f := _), map_sum, map_zsmul, map_nsmul, pull_evc, Category.assoc]

private theorem zpow_fin_sum_eq_prod_zpow {M : Type*} [CommGroup M] (a : M) (f : Fin 4 → ℤ) :
    a ^ (∑ k, f k) = ∏ k, a ^ f k := by
  simp [Fin.sum_univ_four, Fin.prod_univ_four, zpow_add]

private theorem prod_pow_prod_pow_eq_prod_pow_mul {M : Type*} [CommGroup M] (v : Fin 4 → M) (p q : Matrix (Fin 4) (Fin 4) ℤ)
    (i : Fin 4) : ∏ k, (∏ j, v j ^ q k j) ^ p i k = ∏ j, v j ^ (p * q) i j := by
  simp only [Matrix.mul_apply, zpow_fin_sum_eq_prod_zpow, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.mul_comm]

private theorem prod_pow_smul_one_fin_four_apply {M : Type*} [CommGroup M] (v : Fin 4 → M) (c : ℤ) (j : Fin 4) :
    ∏ k, v k ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) j k = v j ^ c := by
  rw [Finset.prod_eq_single j (fun k _ hk => by simp [Matrix.one_apply_ne (Ne.symm hk)]) (by simp)]
  simp

private theorem algebraMap_OmS_eq_algebraMap_comp {M N : Type*} [CommGroup M] [CommGroup N] (fl : M →* N) (fm : N →* M) (m : ℕ)
    (hm : 1 ≤ m) (hlm : ∀ x, fm (fl x) = x ^ m) (hml : ∀ y, fl (fm y) = y ^ m) (α : Matrix (Fin 4) (Fin 4) ℤ)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (X : Fin 4 → M) (Z : Fin 4 → N) (R1 : ∀ i, fl (X i) ^ 2 * ∏ j, Z j ^ α i j = 1)
    (R2 : ∀ j, (∏ k, X k ^ α k j) * fm (Z j) ^ (2 * m) = 1) : (∀ i, X i = 1) ∧ ∀ j, Z j = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * m ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hc] at hα hα'
  have h4 : 1 ≤ 4 * m ^ 2 := by nlinarith
  have hc1 : c + 1 = 4 * m ^ 2 := by rw [hc]; exact Nat.sub_add_cancel h4
  have hZ : ∀ j, Z j = 1 := by
    intro j
    have e2 : (∏ k, fl (X k) ^ α k j) * Z j ^ (m * (2 * m)) = 1 := by
      have h := congrArg fl (R2 j)
      simp only [map_mul, map_prod, map_zpow, map_pow, hml, map_one, ← pow_mul] at h
      exact h
    have e1 : ∀ k, (fl (X k) ^ α k j) ^ 2 = ((∏ j', Z j' ^ α k j') ^ α.transpose j k)⁻¹ := by
      intro k
      rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm (α k j), zpow_mul, zpow_natCast,
        eq_inv_of_mul_eq_one_left (R1 k), inv_zpow, Matrix.transpose_apply]
    have e3 : (∏ k, fl (X k) ^ α k j) ^ 2 = (Z j ^ (c : ℤ))⁻¹ := by
      rw [← Finset.prod_pow]
      simp_rw [e1]
      rw [Finset.prod_inv_distrib, prod_pow_prod_pow_eq_prod_pow_mul, hα, prod_pow_smul_one_fin_four_apply]
    have e4 := congrArg (· ^ 2) e2
    simp only [mul_pow, one_pow, e3, ← pow_mul] at e4
    have e5 : m * (2 * m) * 2 = c + 1 := by rw [hc1]; ring
    rw [e5, pow_succ, zpow_natCast, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul] at e4
    exact e4
  have hX2 : ∀ i, X i ^ (2 * m) = 1 := by
    intro i
    have h := R1 i
    simp only [hZ, one_zpow, Finset.prod_const_one, _root_.mul_one] at h
    have h' := congrArg fm h
    rw [map_pow, hlm, map_one, ← pow_mul, _root_.mul_comm] at h'
    exact h'
  have R2' : ∀ j, ∏ k, X k ^ α k j = 1 := by
    intro j
    have h := R2 j
    simp only [hZ, map_one, one_pow, _root_.mul_one] at h
    exact h
  have hXc : ∀ i, X i ^ c = 1 := by
    intro i
    have h : ∏ j, (∏ k, X k ^ α.transpose j k) ^ α i j = 1 := by
      simp [Matrix.transpose_apply, R2']
    rw [prod_pow_prod_pow_eq_prod_pow_mul, hα', prod_pow_smul_one_fin_four_apply, zpow_natCast] at h
    exact h
  refine ⟨fun i => ?_, hZ⟩
  have h1 : X i ^ (c + 1) = 1 := by
    rw [hc1, show 4 * m ^ 2 = 2 * m * (2 * m) by ring, pow_mul, hX2, one_pow]
  rw [pow_succ, hXc, _root_.one_mul] at h1
  exact h1

theorem zcPair_eq_one (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    {T : Over S} (a : T ⟶ G4 (A ⊗ B))
    (hsym : ∀ (Y : Over S) (_ : Y ⟶ T) (x y : Y ⟶ A), evc hD.isLB x (y ≫ l) = evc hD.isLB y (x ≫ l))
    (h0 : ∀ (Y : Over S) (w : Y ⟶ T) (v : Y ⟶ G4 (A ⊗ B)), zcPair hD.isLB l mu α (w ≫ a) v = 0) :
    a = 1 := by
  haveI := hA.comm
  haveI := hB.comm
  have oneB : ∀ {Y : Over S} (f : Y ⟶ T), f ≫ (1 : T ⟶ B) = 1 := fun f => by simp
  have oneA : ∀ {Y : Over S} (f : Y ⟶ T), f ≫ (1 : T ⟶ A) = 1 := fun f => by simp
  have eq_of_evc {A' B' T' : Over S} [GrpObj A'] [GrpObj B'] {P' : LB (A' ⊗ B').left}
      (h : IsDual A' B' P') {y₁ y₂ : T' ⟶ B'}
      (e : evc h.isLB (fst A' T') (snd A' T' ≫ y₁) =
        evc h.isLB (fst A' T') (snd A' T' ≫ y₂)) : y₁ = y₂ := by
    have hM : (ev P' (fst A' T') (snd A' T' ≫ y₁)).IsLB := pull_isLB h.isLB _
    have ha : IsAdditive (ev P' (fst A' T') (snd A' T' ≫ y₁)) := by
      refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
      rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
    exact (h.univ T' _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
      ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  have dB : ∀ y : T ⟶ B, evc hD.isLB (fst A T) (snd A T ≫ y) = 0 → y = 1 := by
    intro y hy
    apply eq_of_evc hD
    rw [hy, oneB, evc_one_right hD.isLB hD.zero]
  have dA : ∀ y : T ⟶ A, evc hD.isLB (snd B T ≫ y) (fst B T) = 0 → y = 1 := by
    intro y hy
    apply eq_of_evc hD'
    rw [evc_swap hD.isLB hD'.isLB, evc_swap hD.isLB hD'.isLB, hy, oneA,
      IsAdditive.evc_one hD.isLB hD.additive]
  have R1 : ∀ i, postH l (a ≫ prj (A ⊗ B) i ≫ fst A B) ^ 2 *
      ∏ j, (a ≫ prj (A ⊗ B) j ≫ snd A B) ^ α i j = 1 := by
    intro i
    apply dB
    have hz := h0 (A ⊗ T) (snd A T) (mk8 (fun k => if k = i then fst A T else 1) (fun _ => 1))
    rw [zcPair_positionA hD l mu α (snd A T ≫ a) (fst A T) i, hsym (A ⊗ T) (snd A T)] at hz
    show evc hD.isLB (fst A T) (preH (snd A T) (postH l (a ≫ prj (A ⊗ B) i ≫ fst A B) ^ 2 *
      ∏ j, (a ≫ prj (A ⊗ B) j ≫ snd A B) ^ α i j)) = 0
    rw [map_mul, map_pow, map_prod]
    simp only [map_zpow, preH, postH, MonoidHom.mk'_apply]
    rw [evc_right_pow_prod hD hD']
    simpa only [Category.assoc] using hz
  have R2 : ∀ j, (∏ k, (a ≫ prj (A ⊗ B) k ≫ fst A B) ^ α k j) *
      postH mu (a ≫ prj (A ⊗ B) j ≫ snd A B) ^ (2 * m) = 1 := by
    intro j
    apply dA
    have hz := h0 (B ⊗ T) (snd B T) (mk8 (fun _ => 1) (fun k => if k = j then fst B T else 1))
    rw [zcPair_positionB hD l mu α (snd B T ≫ a) (fst B T) j, h₂, comp_id_pow, evc_right_pow hD hD',
      smul_smul] at hz
    show evc hD.isLB (preH (snd B T) ((∏ k, (a ≫ prj (A ⊗ B) k ≫ fst A B) ^ α k j) *
      postH mu (a ≫ prj (A ⊗ B) j ≫ snd A B) ^ (2 * m))) (fst B T) = 0
    rw [map_mul, map_pow, map_prod]
    simp only [map_zpow, preH, postH, MonoidHom.mk'_apply]
    rw [evc_left_prod_pow hD]
    simpa only [Category.assoc] using hz
  obtain ⟨hX, hZ⟩ := algebraMap_OmS_eq_algebraMap_comp (postH l) (postH mu) m hm
    (fun x => by
      show (x ≫ l) ≫ mu = x ^ m
      rw [Category.assoc, h₁, comp_id_pow])
    (fun y => by
      show (y ≫ mu) ≫ l = y ^ m
      rw [Category.assoc, h₂, comp_id_pow])
    α hα hα' (fun i => a ≫ prj (A ⊗ B) i ≫ fst A B) (fun j => a ≫ prj (A ⊗ B) j ≫ snd A B) R1 R2
  apply ext8
  · intro i
    exact (hX i).trans (one_prj_fst i).symm
  · intro i
    exact (hZ i).trans (one_prj_snd i).symm

end PositivityTheory.PrwZar
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Points

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def kLiftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) : Y ⟶ (Over.pullback s).obj G :=
  Over.homMk (pullback.lift v.left Y.hom (Over.w v)) (pullback.lift_snd _ _ _)

theorem kToBase_liftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) :
    toBase G s (kLiftPt s G v) = v :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

theorem kToBase_inj (G : Over S) {Y : Over (Sp Ω)} {a b : Y ⟶ (Over.pullback s).obj G}
    (h : toBase G s a = toBase G s b) : a = b := by
  ext1
  apply pullback.hom_ext
  · simpa [toBase] using congrArg Over.Hom.left h
  · exact (Over.w a).trans (Over.w b).symm

theorem kToBase_comp (G : Over S) {Y Y' : Over (Sp Ω)} (h : Y' ⟶ Y) (a : Y ⟶ (Over.pullback s).obj G) :
    toBase G s (h ≫ a) = (Over.homMk h.left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w h]) :
      Over.mk (Y'.hom ≫ s) ⟶ Over.mk (Y.hom ≫ s)) ≫ toBase G s a :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
theorem kToBase_one (G : Over S) [GrpObj G] {Y : Over (Sp Ω)} :
    toBase G s (1 : Y ⟶ (Over.pullback s).obj G) = 1 := by
  apply Over.OverMorphism.ext
  simp only [toBase, Hom.one_def]
  simp

theorem kLift_sqToBase (G : Over S) {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj G) :
    (lift a u).left ≫ sqToBase G s = (lift (toBase G s a) (toBase G s u)).left := by
  have key : (Over.homMk (lift a u).left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w (lift a u)]) :
      Over.mk (Y.hom ≫ s) ⟶ Over.mk (((Over.pullback s).obj G ⊗ (Over.pullback s).obj G).hom ≫ s)) ≫
        lift (toBase G s (fst _ _)) (toBase G s (snd _ _)) = lift (toBase G s a) (toBase G s u) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← kToBase_comp, lift_fst, lift_fst]
    · rw [Category.assoc, lift_snd, ← kToBase_comp, lift_snd, lift_snd]
  unfold sqToBase
  rw [← key]
  rfl

end Points

variable {Ω : Type} [Field Ω]

theorem kLam_zb_pt (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) a u =
      zcPair hD.isLB l mu α (toBase _ s a) (toBase _ s u) := by
  have k := lam_zb hA hB hD hD' l mu α Ω s L hL e
  have k2 := congrArg (pull (lift a u).left) k
  rw [pull_lam, lift_fst, lift_snd] at k2
  rw [← k2, ← pull_comp, kLift_sqToBase]
  unfold zc
  rw [zcPair_pull, lift_fst, lift_snd]

theorem kEvc_sym (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (s : Sp Ω ⟶ S)
    (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (x y : Over.mk (Y.hom ≫ s) ⟶ A) :
    evc hP x (y ≫ l) = evc hP y (x ≫ l) := by
  haveI := hA.comm
  haveI : IsCommMonObj ((Over.pullback s).obj A) := inferInstance
  have h1 := lam_cL_pt s hP l L hL e (kLiftPt s A x) (kLiftPt s A y)
  have h2 := lam_cL_pt s hP l L hL e (kLiftPt s A y) (kLiftPt s A x)
  rw [kToBase_liftPt, kToBase_liftPt] at h1 h2
  rw [← h1, ← h2]
  unfold lam
  rw [mul_comm (kLiftPt s A x) (kLiftPt s A y)]
  abel

private theorem evc_comp_left_eq_pull {S' : Scheme} {G H Y0 Y1 : Over S'} {P : LB (G ⊗ H).left} (hP : P.IsLB)
    (h : Y1 ⟶ Y0) (a : Y0 ⟶ G) (b : Y0 ⟶ H) : evc hP (h ≫ a) (h ≫ b) = pull h.left (evc hP a b) := by
  unfold evc
  rw [← pull_comp, ← Over.comp_left, comp_lift]

private theorem lam_comp_eq_pull_lift_sub_pull_lift_one {S' : Scheme} {G T0 Y0 : Over S'} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (x : T0 ⟶ G) (g : Y0 ⟶ T0) (u : Y0 ⟶ G) :
    lam (cls L hL) (g ≫ x) u =
      pull (lift g u).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) -
        pull (lift g (1 : Y0 ⟶ G)).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) := by
  rw [GlobalTheory.TripleProd.cls_translDiff hL x]
  simp only [map_sub, ← pull_comp, ← Over.comp_left, comp_mul, lift_fst_assoc, lift_snd]
  rw [_root_.mul_one]
  unfold lam
  abel

private theorem pull_lift_cls_translDiff_eq_zero_of_gen {S' : Scheme} {G T0 Y0 : Over S'} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (x : T0 ⟶ G) (W : T0.left.Opens)
    (hW : ∃ c : ((Out.translDiff G L x).pull ((fst T0 G).left ⁻¹ᵁ W).ι).Gen, c.IsGen)
    (g : Y0 ⟶ T0) (hg : Set.range g.left.base ⊆ W) (u : Y0 ⟶ G) :
    pull (lift g u).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) = 0 := by
  have hD : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  have h0 := (cls_eq_zero_iff (LB.isLB_pull hD ((fst T0 G).left ⁻¹ᵁ W).ι)).2 hW
  rw [cls_pull hD _ (LB.isLB_pull hD _)] at h0
  have hr : Set.range (lift g u).left.base ⊆ Set.range ((fst T0 G).left ⁻¹ᵁ W).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T0 G).left.base ((lift g u).left.base y) ∈ W
    have e1 : (fst T0 G).left.base ((lift g u).left.base y) = g.left.base y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    rw [e1]
    exact hg ⟨y, rfl⟩
  rw [← IsOpenImmersion.lift_fac _ _ hr, pull_comp, h0, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem kTriv_zb' (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.KTriv ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) := by
  intro R _ t x hloc
  have core : ∀ V : (Spec (CommRingCat.of R)).Opens,
      (∃ c : ((Out.translDiff _ (zb mu α s P L) x).pull
        ((fst (Over.mk t) ((Over.pullback s).obj (G4 (A ⊗ B)))).left ⁻¹ᵁ V).ι).Gen, c.IsGen) →
      V.ι ≫ x.left = V.ι ≫ (toUnit (Over.mk t) ≫ η).left := by
    intro V hV
    let Z : Over (Sp Ω) := Over.mk (V.ι ≫ t)
    let j : Z ⟶ Over.mk t := Over.homMk V.ι rfl
    have hxV : j ≫ x = 1 := by
      apply kToBase_inj s
      rw [kToBase_one]
      refine zcPair_eq_one hA hB hD hD' l mu α m hm h₁ h₂ hα hα' (toBase _ s (j ≫ x)) ?_ ?_
      · intro Y w a b
        let Z' : Over (Sp Ω) := Over.mk (w.left ≫ Z.hom)
        let ε : Y ≅ Over.mk (Z'.hom ≫ s) := Over.isoMk (Iso.refl _) (by simpa [Z'] using Over.w w)
        calc evc _ a (b ≫ l) = evc hD.isLB (ε.hom ≫ (ε.inv ≫ a)) (ε.hom ≫ (ε.inv ≫ b ≫ l)) := by simp
          _ = pull ε.hom.left (evc hD.isLB (ε.inv ≫ a) (ε.inv ≫ b ≫ l)) := evc_comp_left_eq_pull _ _ _ _
          _ = pull ε.hom.left (evc hD.isLB (ε.inv ≫ b) ((ε.inv ≫ a) ≫ l)) := by
            rw [← Category.assoc ε.inv b l, kEvc_sym hA hD.isLB l s L hL e (ε.inv ≫ a) (ε.inv ≫ b)]
          _ = evc _ b (a ≫ l) := by
            rw [← evc_comp_left_eq_pull]
            simp
      · intro Y w v
        let Z' : Over (Sp Ω) := Over.mk (w.left ≫ Z.hom)
        let ε : Y ≅ Over.mk (Z'.hom ≫ s) := Over.isoMk (Iso.refl _) (by simpa [Z'] using Over.w w)
        let k : Z' ⟶ Z := Over.homMk w.left rfl
        have hk : ε.inv ≫ w = (Over.homMk k.left
            (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w k]) :
              Over.mk (Z'.hom ≫ s) ⟶ Over.mk (Z.hom ≫ s)) := by
          ext
          simp [ε, k]
          try exact Category.id_comp _
        have hg : Set.range (k ≫ j).left.base ⊆ (V : Set (Spec (CommRingCat.of R))) := by
          rintro _ ⟨y, rfl⟩
          have e2 : (k ≫ j).left = k.left ≫ V.ι := by simp [j]
          rw [e2, Scheme.Hom.comp_apply]
          have hm := Set.mem_range_self (f := V.ι.base) (k.left.base y)
          rwa [Scheme.Opens.range_ι] at hm
        calc zcPair _ l mu α (w ≫ toBase _ s (j ≫ x)) v
            = zcPair hD.isLB l mu α (ε.hom ≫ (ε.inv ≫ w ≫ toBase _ s (j ≫ x))) (ε.hom ≫ (ε.inv ≫ v)) := by
              simp
          _ = pull ε.hom.left (zcPair hD.isLB l mu α (ε.inv ≫ w ≫ toBase _ s (j ≫ x)) (ε.inv ≫ v)) :=
              (zcPair_pull _ _ _ _ _ _ _).symm
          _ = 0 := by
            rw [← Category.assoc, hk, ← kToBase_comp, ← kToBase_liftPt s _ (ε.inv ≫ v),
              ← kLam_zb_pt hA hB hD hD' l mu α s L hL e, ← Category.assoc,
              lam_comp_eq_pull_lift_sub_pull_lift_one (isLB_zb mu α s hD.isLB hL) x (k ≫ j),
              pull_lift_cls_translDiff_eq_zero_of_gen (isLB_zb mu α s hD.isLB hL) x V hV (k ≫ j) hg,
              pull_lift_cls_translDiff_eq_zero_of_gen (isLB_zb mu α s hD.isLB hL) x V hV (k ≫ j) hg, sub_zero, map_zero]
    have h2 : j ≫ (toUnit (Over.mk t) ≫ η[(Over.pullback s).obj (G4 (A ⊗ B))]) =
        (1 : Z ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) := by
      rw [Hom.one_def, ← Category.assoc, comp_toUnit]
    have h3 := congrArg Over.Hom.left (hxV.trans h2.symm)
    exact h3
  choose V hpV hV using hloc
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext ((Spec (CommRingCat.of R)).openCoverOfIsOpenCover V ?_) _ _ (fun p => ?_)
  · exact eq_top_iff.2 (fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hpV p⟩)
  · exact core (V p) (hV p)

theorem kTriv_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.KTriv ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) :=
  kTriv_zb' hA hB hD hD' l mu α s L hL e m hm h₁ h₂ hα hα'

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.OneCompPrj
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]


omit [GrpObj A] [GrpObj B] in
theorem one_comp_prj {G : Over S} [GrpObj G] {Y : Over S} (i : Fin 4) : (1 : Y ⟶ G4 G) ≫ prj G i = 1 := by
  fin_cases i <;> simp [prj]

theorem zc_rigid {P : LB (A ⊗ B).left} (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) :
    pull (lift (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B)) (𝟙 _)).left (zc hD.isLB l mu α) = 0 ∧
      pull (lift (𝟙 _) (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B))).left (zc hD.isLB l mu α) = 0 := by
  have e1 : ∀ {Y : Over S} (t : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) t = 0 :=
    fun t => IsAdditive.evc_one hD.isLB hD.additive t
  have e2 : ∀ {Y : Over S} (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 :=
    fun a => evc_one_right hD.isLB hD.zero a
  have o1 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ A) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  have o2 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ B) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  constructor <;>
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [zc, zcPair, map_add (f := _), map_sum, map_nsmul, map_zsmul, pull_evc, lift_fst_assoc, lift_snd_assoc,
      Category.id_comp, o1, o2, e1, e2, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ExistsQuat
namespace PositivityTheory.PrwZar

theorem exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  have hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]
    push_cast
    ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>
  · rw [hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

end PositivityTheory.PrwZar
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

theorem principal_of_quasiInverse {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (l : A ⟶ B) (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (hD : IsDual A B P) (hD' : IsDual B A (swap P))
    (hpol : GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.IsPolarisation A B P l)
    (hq : ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m) :
    ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c := by
  obtain ⟨m, mu, hm, hmu, h₁, h₂⟩ := hq
  obtain ⟨α, hα, hα'⟩ := exists_quat (4 * m ^ 2 - 1)
  have := hpol.1
  refine ⟨zc hD.isLB l mu α, (zc_rigid hD l mu α).1, (zc_rigid hD l mu α).2, fun Ω _ _ s => ?_⟩
  obtain ⟨L, hL, ha, e⟩ := hpol.2 Ω s
  exact ⟨zb mu α s P L, isLB_zb mu α s hD.isLB hL,
    relAmple_zb hA hB hD hD' l mu α Ω s L hL e ha g hgA hgB m hm h₁ h₂ hα hα',
    kTriv_zb hA hB hD hD' l mu α Ω s L hL e m hm h₁ h₂ hα hα',
    lam_zb hA hB hD hD' l mu α Ω s L hL e⟩


open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin in
theorem zarhinStatement_of_dual_cube_qiR (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem)
    (hQ : QuasiInverseR) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement := by
  intro C _ _ v R _ _ hv A _ L hA hL ha
  have := isLocalRing_integers hv
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeDual.isAdditive_lam hC hA hL hΛ
  obtain ⟨B, _, P, hB, hdim, h₁, h₂⟩ := hD _ A hA
  obtain ⟨x, hx, -⟩ := h₁.univ A (abelian₂ A L) hΛ a₁
  have hm := isMonHom_of_classifying _ A A B (abelian₂ A L) P h₁ h₂.additive hΛ a₂ x hx
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim R A hA
  have hpol := isPolarisation_of_relAmple h₁.isLB hm hL ha hx
  obtain ⟨c, hc⟩ := principal_of_quasiInverse A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol
    (hQ C v R hv A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol)
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  obtain ⟨M, hM, m₁, m₂, m₃, m₄, -⟩ := SymB.symmetricBundle hD hC C v R hv _ h4 c hc
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim R _ h4
  have := hA.comm
  have := hB.comm
  refine ⟨⟨G4 (A ⊗ B), h4, g', hg', M, hM, m₁, m₂, m₃, m₄⟩, lift (lift (𝟙 A) 1) 1, fst _ _ ≫ fst _ _,
    inferInstance, inferInstance, by simp⟩

theorem zarhinStatement_of_dual_cube (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) :
    GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  zarhinStatement_of_dual_cube_qiR hD hC quasiInverseR

end PositivityTheory.PrwZar
end
end

namespace PositivityTheory.HtPt.Narrow

theorem zarhin (hD : GlobalTheory.Published.DualAbelianScheme) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  PositivityTheory.PrwZar.zarhinStatement_of_dual_cube hD GlobalTheory.SpreadingModels.cubeTheorem_holds

end PositivityTheory.HtPt.Narrow

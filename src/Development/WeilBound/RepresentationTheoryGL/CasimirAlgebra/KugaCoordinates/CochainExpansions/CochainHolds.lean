module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.EtaExpand
section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.SumSumProd
noncomputable section

open Complex

namespace PositivityTheory.Rg.Cz.Coch

variable {H V : Type*} [AddCommGroup V] [Module ℂ V]

def cEv {N : ℕ} (F : (Fin N → H) → V) (A B : Fin N → H) : V :=
  ∑ S : Fin N → Bool, (∏ k, if S k then (1 : ℂ) else -I) • F (fun k => if S k then A k else B k)

theorem cEv_zero {N : ℕ} (A B : Fin N → H) : cEv (fun _ => (0 : V)) A B = 0 := by
  simp [cEv]

theorem cEv_sum {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℤ) (F : ι → (Fin N → H) → V) (A B : Fin N → H) :
    cEv (fun v => ∑ i ∈ s, c i • F i v) A B = ∑ i ∈ s, c i • cEv (F i) A B := by
  unfold cEv
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => ?_
  exact smul_comm _ _ _

theorem cEv_perm {N : ℕ} (F : (Fin N → H) → V) (σ : Equiv.Perm (Fin N)) (A B : Fin N → H) :
    cEv (fun v => F (fun i => v (σ i))) A B = cEv F (fun i => A (σ i)) (fun i => B (σ i)) := by
  unfold cEv
  refine Fintype.sum_equiv ⟨fun S => S ∘ σ, fun T => T ∘ σ.symm, fun S => by funext x; simp,
    fun T => by funext x; simp⟩ _ _ fun S => ?_
  simp only [Equiv.coe_fn_mk, Function.comp_apply]
  congr 1
  exact (Equiv.prod_comp σ (fun k => if S k then (1 : ℂ) else -I)).symm

theorem cEv_prod2 {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → Fin N → H → ℂ) (c : ι → κ → V)
    (A B : Fin N → H) :
    cEv (fun v => ∑ x, ∑ y, (∏ k, f x y k (v k)) • c x y) A B =
      ∑ x, ∑ y, (∏ k, (f x y k (A k) - I * f x y k (B k))) • c x y := by
  unfold cEv
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  have e : ∀ k, f x y k (A k) - I * f x y k (B k) =
      ∑ b : Bool, (if b then (1 : ℂ) else -I) * f x y k (if b then A k else B k) := by
    intro k; simp; ring
  simp_rw [e]
  rw [Fintype.prod_sum]

theorem sum_sum_prod {N : ℕ} {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R] (g : Fin N → α → β → R) :
    ∑ A : Fin N → α, ∑ B : Fin N → β, ∏ k, g k (A k) (B k) = ∏ k, ∑ a, ∑ b, g k a b := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Fintype.prod_sum]

end PositivityTheory.Rg.Cz.Coch

end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.Coch

open PositivityTheory.Rg.Cz

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def ent (τ : E →+* ℂ) (i j : Fin a) : Herm E a →ₗ[ℝ] ℂ where
  toFun X := coord τ (X.1 i j)
  map_add' X Y := by simp
  map_smul' c X := (coordL τ).map_smul c (X.1 i j)

theorem ent_apply (τ : E →+* ℂ) (i j : Fin a) (X : Herm E a) : ent τ i j X = coord τ (X.1 i j) := rfl

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {q N : ℕ}

def vec (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (I' I'' : Fin N → Fin a) : TV a M (Fin q) :=
  fun I => η (Sum.elim I (Sum.elim I' I''))

def mm (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) :
    (Fin N → Herm E a) →ₘₗ[ℝ] TV a M (Fin q) :=
  ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a,
    ((LinearMap.toSpanSingleton ℂ _ (vec η I' I'')).restrictScalars ℝ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ (Fin N) ℂ).compLinearMap fun k => ent (tl k) (I'' k) (I' k))

theorem mm_apply (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (X : Fin N → Herm E a)
    (I : Fin q → Fin a) : mm tl η X I = ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a,
      (∏ k, coord (tl k) ((X k).1 (I'' k) (I' k))) • η (Sum.elim I (Sum.elim I' I'')) := by
  simp [mm, Finset.sum_apply, vec, ent_apply]

def om (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) : Herm E a [⋀^Fin N]→ₗ[ℝ] TV a M (Fin q) :=
  MultilinearMap.alternatization (mm tl η)

theorem om_apply (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (X : Fin N → Herm E a)
    (I : Fin q → Fin a) :
    om tl η X I = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ)) • mm tl η (fun i => X (σ i)) I := by
  rw [om, MultilinearMap.alternatization_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, Units.smul_def, MultilinearMap.domDomCongr_apply]

theorem om_swap (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (p p' : Fin q)
    (h : pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η) (X : Fin N → Herm E a) :
    pm (Equiv.swap p p') (om tl η X) = -om tl η X := by
  funext I
  rw [pm_apply, Pi.neg_apply, om_apply, om_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← smul_neg, mm_apply, mm_apply, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I'' _ => ?_
  rw [← smul_neg]
  congr 1
  have e : Sum.elim (I ∘ Equiv.swap p p') (Sum.elim I' I'') =
      Sum.elim I (Sum.elim I' I'') ∘ Equiv.swap (Sum.inl p) (Sum.inl p') := by
    funext x
    rcases x with x | x
    · simp [Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · simp [Equiv.swap_apply_def]
  rw [e]
  exact congrFun h _

theorem intersection_update_fsHerm_neg_one (τ : E →+* ℂ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) (a' b : Fin a) :
    ∑ x, ∑ y, coord τ ((k.1 * X * star k.1) y x) * kap E a τ k x b * star (kap E a τ k y a') = coord τ (X a' b) := by
  set U := kap E a τ k with hUdef
  have hs : (star k.1).map (coord τ) = Uᴴ := by
    ext i j
    simp [U, kap, Matrix.star_apply, Matrix.conjTranspose_apply, J.coord_star]
  have hU : Uᴴ * U = 1 := by
    have h1 : star k.1 * k.1 = 1 := Matrix.UnitaryGroup.star_mul_self k
    have h2 := congrArg (fun m => m.map (coord τ)) h1
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [hs] at h2
    exact h2
  have hm : (k.1 * X * star k.1).map (coord τ) = U * X.map (coord τ) * Uᴴ := by
    rw [Matrix.map_mul, Matrix.map_mul, hs]
    rfl
  have hc : ∀ y x, coord τ ((k.1 * X * star k.1) y x) = (U * X.map (coord τ) * Uᴴ) y x := fun y x => by
    rw [← hm]; rfl
  simp_rw [hc]
  have key : (Uᴴ * (U * X.map (coord τ) * Uᴴ) * U) a' b = coord τ (X a' b) := by
    rw [show Uᴴ * (U * X.map (coord τ) * Uᴴ) * U = (Uᴴ * U) * X.map (coord τ) * (Uᴴ * U) by
      simp only [Matrix.mul_assoc], hU, Matrix.one_mul, Matrix.mul_one, Matrix.map_apply]
  rw [← key]
  generalize U * X.map (coord τ) * Uᴴ = Z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem kap_bar [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (k : Kinf E a) (x y : Fin a) :
    kap E a (barE E τ) k x y = star (kap E a τ k x y) := by
  simp only [kap, Matrix.map_apply]
  exact J.coord_conjugate τ _

theorem eta_expand [_root_.NumberField.IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ)) (ρ : Kinf E a → Module.End ℂ M)
    (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) (k : Kinf E a) (I : Fin q → Fin a) (I' I'' : Fin N → Fin a) :
    η (Sum.elim I (Sum.elim I' I'')) = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
      ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
        ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j)))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
  conv_lhs => rw [← h2 k]
  rw [actT_apply]
  let e : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)) ≃ (Fin q ⊕ (Fin N ⊕ Fin N) → Fin a) :=
    (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ _).symm).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
  refine (Fintype.sum_equiv e _ _ (fun w => ?_)).symm
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [lab3, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, kap_bar]
  rfl

theorem coef_id (tl : Fin N → (E →+* ℂ)) (k : Kinf E a) (Y : Fin N → Herm E a) (K : ℂ) (A' B' : Fin N → Fin a) :
    ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
      (K * ((∏ j, kap E a (tl j) k (I' j) (B' j)) * ∏ j, star (kap E a (tl j) k (I'' j) (A' j)))) =
      K * ∏ j, coord (tl j) ((Y j).1 (A' j) (B' j)) := by
  have h : ∀ I' I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
      (K * ((∏ j, kap E a (tl j) k (I' j) (B' j)) * ∏ j, star (kap E a (tl j) k (I'' j) (A' j)))) =
      K * ∏ j, (coord (tl j) ((k.1 * (Y j).1 * star k.1) (I'' j) (I' j)) * kap E a (tl j) k (I' j) (B' j) *
        star (kap E a (tl j) k (I'' j) (A' j))) := by
    intro I' I''
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [adHerm]
    ring
  simp_rw [h, ← Finset.mul_sum]
  congr 1
  rw [sum_sum_prod (fun j x y => coord (tl j) ((k.1 * (Y j).1 * star k.1) y x) * kap E a (tl j) k x (B' j) *
    star (kap E a (tl j) k y (A' j)))]
  exact Finset.prod_congr rfl fun j _ => intersection_update_fsHerm_neg_one (tl j) k (Y j).1 (A' j) (B' j)

theorem mm_equiv [_root_.NumberField.IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ)) (ρ : Kinf E a → Module.End ℂ M)
    (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) (k : Kinf E a) (Y : Fin N → Herm E a) :
    mm tl η (fun i => adHerm k (Y i)) = actT lab (kap E a) ρ k (mm tl η Y) := by
  funext I
  rw [mm_apply, actT_apply]
  calc _ = ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        ((∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
          ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
            ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j))))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun I'' _ => ?_
        rw [eta_expand lab tl ρ η h2 k I I' I'', Finset.smul_sum]
        simp_rw [smul_smul]
    _ = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        (∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
          ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
            ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j))))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        simp_rw [Finset.sum_smul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun I' _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ∏ j, coord (tl j) ((Y j).1 (w.2.2 j) (w.2.1 j))) •
          ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [coef_id]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J1 _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [mm_apply, map_sum, Finset.smul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun B' _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun A' _ => ?_
        rw [map_smul, smul_smul]

theorem om_cochain [_root_.NumberField.IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ))
    (ρ : Kinf E a → Module.End ℂ M) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) :
    IsCochain (actT lab (kap E a) ρ) (om tl η) := by
  intro k X
  set_option synthInstance.maxHeartbeats 100000 in
    rw [om, MultilinearMap.alternatization_apply, MultilinearMap.alternatization_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, MultilinearMap.domDomCongr_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  exact mm_equiv lab tl ρ η h2 k (fun i => X (σ i))

end PositivityTheory.Rg.Cz.Coch

end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.Coch

open PositivityTheory.Rg.Cz

variable {E : Type} [Field E] [NumberField E] {a : ℕ}
variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {q N : ℕ}

def hY (τ : E →+* ℂ) (j i : Fin a) (z : ℂ) : Herm E a :=
  ⟨Matrix.single j i (atEmb τ z) + star (Matrix.single j i (atEmb τ z)), IsSelfAdjoint.add_star_self _⟩

omit [NumberField E] in
theorem hY_ent [_root_.NumberField.IsTotallyComplex E] (τ τ' : E →+* ℂ) (h : τ' ≠ barE E τ) (j i j' i' : Fin a) :
    coord τ' ((hY τ j i (1 / 2)).1 j' i') - Complex.I * coord τ' ((hY τ j i (Complex.I / 2)).1 j' i') =
      if τ' = τ ∧ j' = j ∧ i' = i then 1 else 0 := by
  have hc : ∀ z, coord τ' (atEmb τ z) = if τ' = τ then z else 0 := fun z => by
    by_cases h1 : τ' = τ
    · subst τ'
      rw [if_pos rfl, coord_atEmb]
    · have h2 : τ' ≠ ComplexEmbedding.conjugate τ := h
      have hp : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ := fun hp => by
        rcases InfinitePlace.mk_eq_iff.1 hp with hp | hp
        · exact h1 hp
        · exact h2 (by rw [← hp]; ext; simp)
      rw [if_neg h1]
      unfold coord atEmb
      by_cases h3 : (InfinitePlace.mk τ').embedding = τ'
      · rw [if_pos h3]; simp [hp]
      · rw [if_neg h3]; simp [hp]
  have he : ∀ z, coord τ' ((hY τ j i z).1 j' i') =
      (if j = j' ∧ i = i' then coord τ' (atEmb τ z) else 0) +
        (if j = i' ∧ i = j' then star (coord τ' (atEmb τ z)) else 0) := by
    intro z
    simp only [hY, Matrix.add_apply, Matrix.star_apply, Matrix.single_apply]
    rw [map_add (f := _)]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp [PositivityTheory.Rg.Cz.J.coord_star]
  rw [he, he, hc, hc]
  clear he hc
  by_cases h1 : τ' = τ
  · subst h1
    clear h
    have hP : (τ' = τ' ∧ j' = j ∧ i' = i) ↔ (j = j' ∧ i = i') :=
      ⟨fun h => ⟨h.2.1.symm, h.2.2.symm⟩, fun h => ⟨rfl, h.1.symm, h.2.symm⟩⟩
    rw [if_congr hP rfl rfl]
    by_cases hp : j = j' ∧ i = i' <;> by_cases hq : j = i' ∧ i = j'
    · simp only [if_pos hp, if_pos hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_pos hp, if_neg hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_neg hp, if_pos hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_neg hp, if_neg hq]; simp
  · simp [h1]

theorem om_ne [_root_.NumberField.IsTotallyComplex E] (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h1 : ∀ k k', tl k ≠ barE E (tl k')) (h3 : altPair tl η ≠ 0) : om tl η ≠ 0 := by
  intro h0
  apply h3
  funext J
  set I : Fin q → Fin a := fun p => J (Sum.inl p)
  set P : Fin N → Fin a := fun j => J (Sum.inr (Sum.inl j))
  set Q : Fin N → Fin a := fun j => J (Sum.inr (Sum.inr j))
  let A : Fin N → Herm E a := fun j => hY (tl j) (Q j) (P j) (1 / 2)
  let B : Fin N → Herm E a := fun j => hY (tl j) (Q j) (P j) (Complex.I / 2)
  have hz : cEv (fun v => om tl η v I) A B = 0 := by
    simp only [h0, AlternatingMap.zero_apply, Pi.zero_apply]
    exact cEv_zero (V := M) A B
  have e2 : ∀ A B : Fin N → Herm E a, cEv (fun v => mm tl η v I) A B = ∑ x : Fin N → Fin a, ∑ y : Fin N → Fin a,
      (∏ k, (coord (tl k) ((A k).1 (y k) (x k)) - Complex.I * coord (tl k) ((B k).1 (y k) (x k)))) •
        η (Sum.elim I (Sum.elim x y)) := fun A B => by
    have := cEv_prod2 (V := M) (fun x y k (h : Herm E a) => coord (tl k) (h.1 (y k) (x k)))
      (fun x y => η (Sum.elim I (Sum.elim x y))) A B
    rw [show (fun v => mm tl η v I) = fun v => ∑ x : Fin N → Fin a, ∑ y : Fin N → Fin a,
      (∏ k, (fun x y k (h : Herm E a) => coord (tl k) (h.1 (y k) (x k))) x y k (v k)) •
        (fun x y => η (Sum.elim I (Sum.elim x y))) x y from funext fun v => mm_apply tl η v I]
    exact this
  have e3 : ∀ σ : Equiv.Perm (Fin N), cEv (fun v => mm tl η (fun i => v (σ i)) I) A B =
      if ∀ k, tl k = tl (σ k) then η (Sum.elim I (Sum.elim (fun k => P (σ k)) (fun k => Q (σ k)))) else 0 := by
    intro σ
    rw [cEv_perm (V := M) (fun v => mm tl η v I), e2]
    have hp : ∀ x y : Fin N → Fin a, (∏ k, (coord (tl k) ((A (σ k)).1 (y k) (x k)) -
        Complex.I * coord (tl k) ((B (σ k)).1 (y k) (x k)))) =
        if (∀ k, tl k = tl (σ k)) ∧ x = (fun k => P (σ k)) ∧ y = (fun k => Q (σ k)) then 1 else 0 := by
      intro x y
      rw [Finset.prod_congr rfl fun k _ => hY_ent (tl (σ k)) (tl k) (h1 k (σ k)) (Q (σ k)) (P (σ k)) (y k) (x k),
        Finset.prod_boole]
      congr 1
      simp only [Finset.mem_univ, true_implies, funext_iff]
      exact propext ⟨fun h => ⟨fun k => (h k).1, fun k => (h k).2.2, fun k => (h k).2.1⟩,
        fun ⟨h1, h2, h3⟩ k => ⟨h1 k, h3 k, h2 k⟩⟩
    simp only [hp, ite_and, ite_smul, one_smul, zero_smul]
    by_cases hσ : ∀ k, tl k = tl (σ k)
    · simp only [eq_true hσ, if_true]
      rw [Fintype.sum_eq_single (fun k => P (σ k)) (fun x hx => by simp only [if_neg hx, Finset.sum_const_zero])]
      rw [Fintype.sum_eq_single (fun k => Q (σ k)) (fun y hy => by simp only [if_neg hy, ite_self])]
      simp only [if_true]
    · simp only [eq_false hσ, if_false, Finset.sum_const_zero]
  have hJ : ∀ σ : Equiv.Perm (Fin N), J ∘ dbl σ = Sum.elim I (Sum.elim (fun k => P (σ k)) (fun k => Q (σ k))) := by
    intro σ
    funext x
    rcases x with x | x | x <;> rfl
  symm
  rw [Pi.zero_apply, ← hz, show (fun v => om tl η v I) = fun v => ∑ σ : Equiv.Perm (Fin N),
    ((Equiv.Perm.sign σ : ℤ)) • mm tl η (fun i => v (σ i)) I from funext fun v => om_apply tl η v I, cEv_sum (V := M)]
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply, colG, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [e3 σ]
  by_cases hσ : ∀ k, tl k = tl (σ k)
  · rw [if_pos hσ, if_pos fun p => (hσ p).symm, LinearMap.smul_apply, Pi.smul_apply, pm_apply, hJ,
      Int.cast_smul_eq_zsmul]
  · rw [if_neg hσ, if_neg fun h => hσ fun p => (h p).symm, smul_zero]

theorem cochain_holds : Cochain := by
  intro E _ _ _ a M _ _ _ _ ρ q N lab tl η h1 h2 h3
  exact ⟨om tl η, om_ne tl η h1 h3, om_cochain lab tl ρ η h2, fun p p' h X => om_swap tl η p p' h X⟩

end PositivityTheory.Rg.Cz.Coch

end

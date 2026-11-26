module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GrMIff
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have s0 : sg R 0 = 1 := pow_zero _
  have s1 : sg R 1 = -1 := pow_one _
  have e : (0 : ZMod 2) - 1 = 1 := by decide
  rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
  · rw [sub_self, s0, one_mul]
  · rw [e, s0, one_mul]
  · rw [sub_zero, s0, mul_one]
  · rw [sub_self, s0, s1, neg_mul_neg, one_mul]

private theorem sg_sq (R : Type) [CommRing R] (i : ZMod 2) : sg R i * sg R i = 1 := by
  rw [← sg_sub, sub_self]
  exact pow_zero _

private def sgM (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun a => sg R (α a)

private theorem sgM_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : sgM R α * sgM R α = 1 := by
  simp only [sgM, Matrix.diagonal_mul_diagonal, sg_sq, Matrix.diagonal_one]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ (σ : R →+* R).mapMatrix M = sgM R α * M * sgM R β := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [sgM, sgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show σ (M a b) = sg R (α a - β b) * M a b ↔ σ (M a b) = _
  rw [sg_sub, mul_right_comm]

private theorem grM_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) (h' : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff] at h h' ⊢
  rw [map_mul, h, h']
  calc sgM R α * M * sgM R β * (sgM R β * N * sgM R γ)
      = sgM R α * M * (sgM R β * sgM R β) * N * sgM R γ := by simp only [Matrix.mul_assoc]
    _ = sgM R α * (M * N) * sgM R γ := by rw [sgM_sq, Matrix.mul_one, Matrix.mul_assoc _ M]

private theorem grM_inv {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (h : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff] at h ⊢
  have h1 : (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) *
      (σ : R →+* R).mapMatrix ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sgM R β * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sgM R α *
      (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [h]
    calc _ = sgM R β * (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (sgM R α * sgM R α) *
          (g : Matrix (Fin 3) (Fin 3) R)) * sgM R β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [sgM_sq, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, sgM_sq]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem grM_J {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) :
    GrM σ pq pq (Jmat (R := R) 3) := by
  intro a b
  unfold Jmat
  split_ifs with e
  · have : pq a - pq b = 0 := by
      subst e
      revert a
      decide
    rw [this]
    show σ 1 = sg R 0 * 1
    rw [map_one, mul_one]
    exact (pow_zero _).symm
  · exact Submodule.zero_mem _

private theorem grM_tr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) : GrM σ β α Mᵀ := by
  intro a b
  have e : σ (M b a) = sg R (α b - β a) * M b a := h b a
  show σ (M b a) = sg R (β a - α b) * M b a
  rw [e, sg_sub, sg_sub, mul_comm (sg R (α b))]

theorem UpperTheory.V.Fr.ep_grm :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R), (∀ α, GrM σ α α 1) ∧ (∀ α β M N, GrM σ α β M → GrM σ α β N → GrM σ α β (M - N)) ∧ (∀ α β γ M N, GrM σ α β M → GrM σ β γ N → GrM σ α γ (M * N)) ∧ (∀ α β (g : GL (Fin 3) R), GrM σ α β (g : Matrix (Fin 3) (Fin 3) R) → GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) ∧ ∀ (e : ℤˣ) (g : GL (Fin 3) R), GrM σ pq pq (g : Matrix (Fin 3) (Fin 3) R) → GrM σ pq pq ((sgnAct (m := 3) (R := R) e g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O R _ _ _ σ
  refine ⟨fun α => ?_, fun α β M N h h' a b => Submodule.sub_mem _ (h a b) (h' a b), grM_mul σ, grM_inv σ,
    fun e g h => ?_⟩
  · rw [grM_iff, map_one, Matrix.mul_one, sgM_sq]
  · rcases Int.units_eq_one_or e with rfl | rfl
    · rwa [sgnAct_one]
    · rw [sgnAct_neg_one, theta_val]
      exact grM_mul σ _ pq _ _ _ (grM_mul σ _ pq _ _ _ (grM_J σ) (grM_tr σ _ _ _ (grM_inv σ _ _ g h))) (grM_J σ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGlift
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section Av

variable {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]

private def av (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) (x : C') : C' := h • (x + sg C' j * σ' x)

private theorem sg_map (p : C' →ₐ[O] C) (j : ZMod 2) : p (sg C' j) = sg C j := by
  simp [sg]

private theorem av_zero (h : O) (σ' : C' →ₐ[O] C') (j : ZMod 2) : av h σ' j 0 = 0 := by
  simp [av]

variable [IsLocalRing O] [IsCO O C']

variable [IsCO O C]

end Av

private theorem sg_sub_eq_mul {R : Type} [CommRing R] (j k : ZMod 2) : sg R (j - k) = sg R j * sg R k := by
  obtain rfl | rfl : j = 0 ∨ j = 1 := by revert j; decide
  all_goals obtain rfl | rfl : k = 0 ∨ k = 1 := by revert k; decide
  all_goals simp [sg, show (0:ZMod 2) - 1 = 1 from rfl, show (1:ZMod 2) - 1 = 0 from rfl, ZMod.val_one]

private theorem sg_mul_self_eq_one {R : Type} [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  unfold sg
  rw [← pow_add, ← two_mul, pow_mul]
  simp

private theorem grM_iff_map_eq_diagonal_mul_mul_diagonal {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ M.map σ = Matrix.diagonal (fun a => sg R (α a)) * M * Matrix.diagonal (fun b => sg R (β b)) := by
  constructor
  · intro hM
    ext a b
    have e : σ (M a b) = sg R (α a - β b) * M a b := hM a b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, e, sg_sub_eq_mul]
    ring
  · intro hM a b
    have e := congrFun (congrFun hM a) b
    simp only [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    show σ (M a b) = sg R (α a - β b) * M a b
    rw [e, sg_sub_eq_mul]
    ring

private theorem diagonal_sg_mul_diagonal_sg_mul_cancel {R : Type} [CommRing R] (α : Fin 3 → ZMod 2) (X : Matrix (Fin 3) (Fin 3) R) :
    Matrix.diagonal (fun a => sg R (α a)) * (Matrix.diagonal (fun a => sg R (α a)) * X) = X := by
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp only [sg_mul_self_eq_one]
  rw [Matrix.diagonal_one, Matrix.one_mul]

private theorem grM_mul_of_grM_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (hM : GrM σ α β M) (hN : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hM hN ⊢
  have e : (M * N).map σ = M.map σ * N.map σ := Matrix.map_mul (f := (σ : R →+* R))
  rw [e, hM, hN]
  simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]

private theorem grM_gl_inv_of_grM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (hg : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff_map_eq_diagonal_mul_mul_diagonal] at hg ⊢
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hG
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi]; simp
  have hGGi : G * Gi = 1 := by rw [hG, hGi]; simp
  have e : (Gi * G).map σ = Gi.map σ * G.map σ := Matrix.map_mul (f := (σ : R →+* R))
  have e1 : Gi.map σ * G.map σ = 1 := by
    rw [← e, hGiG]
    simp
  have key : Matrix.diagonal (fun a => sg R (α a)) * G * Matrix.diagonal (fun b => sg R (β b)) *
      (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a))) = 1 := by
    simp only [Matrix.mul_assoc, diagonal_sg_mul_diagonal_sg_mul_cancel]
    rw [← Matrix.mul_assoc G, hGGi, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    simp only [sg_mul_self_eq_one]
    exact Matrix.diagonal_one
  calc Gi.map σ
      = Gi.map σ * (G.map σ *
        (Matrix.diagonal (fun b => sg R (β b)) * Gi * Matrix.diagonal (fun a => sg R (α a)))) := by
        rw [hg, key, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

private theorem av_mem_evp_of_involutive {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (h : O) (σ' : R →ₐ[O] R)
    (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (x : R) : av h σ' j x ∈ evp σ' j := by
  show σ' (av h σ' j x) = sg R j * av h σ' j x
  simp only [av, map_smul, map_add (f := _), map_mul, hinv, sg_map σ' j]
  rw [mul_smul_comm]
  congr 1
  linear_combination (-(σ' x)) * sg_mul_self_eq_one (R := R) j

private theorem map_av_eq_map_of_map_mem_evp {O C' C : Type} [CommRing O] [CommRing C'] [Algebra O C'] [CommRing C] [Algebra O C]
    (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C) (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1)
    (j : ZMod 2) (x : C') (hx : p x ∈ evp σ j) : p (av h σ' j x) = p x := by
  have hx' : σ (p x) = sg C j * p x := hx
  simp only [av, map_smul, map_add (f := _), map_mul, hcomm, hx', sg_map p j]
  rw [Algebra.smul_def]
  have h2 : algebraMap O C h * 2 = 1 := by
    rw [← map_ofNat (algebraMap O C) 2, ← map_mul, hh, map_one]
  linear_combination (p x) * h2 + (algebraMap O C h * p x) * sg_mul_self_eq_one (R := C) j

private theorem isUnit_of_isUnit_algHom_map_of_isCO {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (x : C') (hx : IsUnit (p x)) : IsUnit x := by
  by_contra hx'
  have hxm : x ∈ maximalIdeal C' := (IsLocalRing.mem_maximalIdeal x).mpr hx'
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (R := C) (p x)
  have hau : IsUnit (algebraMap O C a) := by
    by_contra hna
    have h1 : algebraMap O C a ∈ maximalIdeal C := (IsLocalRing.mem_maximalIdeal _).mpr hna
    have h2 : p x ∈ maximalIdeal C := by simpa using Ideal.add_mem _ ha h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h2) hx
  haveI := IsCO.isLocalHom (O := O) (R := C)
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit (algebraMap O C) a hau
  have h1 : IsUnit (1 - algebraMap O C' ↑u⁻¹ * x) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hxm))
  have h2 := h1.map p
  have h3 : p (1 - algebraMap O C' ↑u⁻¹ * x) = -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) := by
    rw [map_sub, map_one, map_mul, AlgHom.commutes]
    have : algebraMap O C ↑u⁻¹ * algebraMap O C ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-1 : C) * this
  rw [h3] at h2
  have h4 : -(algebraMap O C ↑u⁻¹ * (p x - algebraMap O C ↑u)) ∈ maximalIdeal C :=
    (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ ha)
  exact ((IsLocalRing.mem_maximalIdeal _).mp h4) h2

private theorem av_sub_av_mem_maximalIdeal_pow {O C' : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (N : ℕ) (x y : C')
    (hxy : x - y ∈ maximalIdeal C' ^ N) : av h σ' j x - av h σ' j y ∈ maximalIdeal C' ^ N := by
  have hm : Ideal.map σ' (maximalIdeal C') ≤ maximalIdeal C' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    intro hu
    apply hz
    have := hu.map σ'
    rwa [hinv] at this
  have hmN : Ideal.map σ' (maximalIdeal C' ^ N) ≤ maximalIdeal C' ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have hσ : σ' (x - y) ∈ maximalIdeal C' ^ N := hmN (Ideal.mem_map_of_mem _ hxy)
  have e : av h σ' j x - av h σ' j y = algebraMap O C' h * ((x - y) + sg C' j * σ' (x - y)) := by
    simp only [av, Algebra.smul_def, map_sub]
    ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hσ))

private theorem adicCont_av_comp {Γ O C' : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing C']
    [Algebra O C'] [IsCO O C'] (h : O) (σ' : C' →ₐ[O] C') (hinv : ∀ y, σ' (σ' y) = y) (j : ZMod 2) (f : Γ → C')
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C') (fun s => av h σ' j (f s)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := maximalIdeal C' ^ N)
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (f g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal C' ^ N) (av h σ' j (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal C' ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq]
    apply av_sub_av_mem_maximalIdeal_pow h σ' hinv j N
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem exists_gl_eq_av_entries_and_map_eq {O C' C : Type} [CommRing O] [IsLocalRing O] [CommRing C'] [Algebra O C'] [IsCO O C']
    [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C)
    (hcomm : ∀ y, p (σ' y) = σ (p y)) (h : O) (hh : h * 2 = 1) (α β : Fin 3 → ZMod 2) (X : GL (Fin 3) C')
    (hX : GrM σ α β ((X : Matrix (Fin 3) (Fin 3) C').map p)) :
    ∃ Y : GL (Fin 3) C', (Y : Matrix (Fin 3) (Fin 3) C') =
        Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) ∧
      Matrix.GeneralLinearGroup.map (p : C' →+* C) Y = Matrix.GeneralLinearGroup.map (p : C' →+* C) X := by
  set M : Matrix (Fin 3) (Fin 3) C' := Matrix.of (fun a b => av h σ' (α a - β b) ((X : Matrix (Fin 3) (Fin 3) C') a b)) with hM
  have hmap : M.map p = (X : Matrix (Fin 3) (Fin 3) C').map p := by
    ext a b
    exact map_av_eq_map_of_map_mem_evp p σ' σ hcomm h hh _ _ (hX a b)
  have hXu : IsUnit (X : Matrix (Fin 3) (Fin 3) C').det := (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_algHom_map_of_isCO p
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, hmap, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    exact hXu.map p
  refine ⟨Matrix.nonsingInvUnit M hdet, rfl, ?_⟩
  exact Units.ext hmap

theorem UpperTheory.V.Fr.ep_glift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (σ : C →ₐ[O] C), (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) → ∀ (B : Box F 3 C) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → SetLift p B → ∃ D : SetLift p B, D.Gr σ' π := by
  intro l _ k _ F O _ _ _ _ h2 C' _ _ _ C _ _ _ p σ' σ hinv hcomm B π hB D
  obtain ⟨h, hh⟩ : ∃ h : O, h * 2 = 1 := ⟨_, h2.val_inv_mul⟩
  have gr_r : ∀ s, GrM σ pq pq ((D.r s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro s
    have e : (D.r s : Matrix (Fin 3) (Fin 3) C').map p = ((B.r s).left : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.r_map s]
      rfl
    rw [e]
    exact hB.r s
  have gr_g : ∀ v, GrM σ (π v) pq ((D.g v : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v
    have e : (D.g v : Matrix (Fin 3) (Fin 3) C').map p = ((B.g v : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.g_map v]
      rfl
    rw [e]
    exact hB.g v
  have gr_t : ∀ v s, GrM σ (π v) (π v) ((D.t v s : Matrix (Fin 3) (Fin 3) C').map p) := by
    intro v s
    have e : (D.t v s : Matrix (Fin 3) (Fin 3) C').map p =
        ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
      rw [← D.t_map v s]
      rfl
    rw [e, Units.val_mul, Units.val_mul]
    exact grM_mul_of_grM_of_grM σ _ _ _ _ _ (grM_mul_of_grM_of_grM σ _ _ _ _ _ (hB.g v) (hB.r _)) (grM_gl_inv_of_grM σ _ _ _ (hB.g v))
  choose r' hr' hr'm using fun s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh pq pq (D.r s) (gr_r s)
  choose g' hg' hg'm using fun v => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) pq (D.g v) (gr_g v)
  choose t' ht' ht'm using fun v s => exists_gl_eq_av_entries_and_map_eq p σ' σ hcomm h hh (π v) (π v) (D.t v s) (gr_t v s)
  refine ⟨⟨r', ?_, fun s => (hr'm s).trans (D.r_map s), g', fun v => (hg'm v).trans (D.g_map v), t', ?_, ?_,
    fun v s => (ht'm v s).trans (D.t_map v s)⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i j
    simp only [hr', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.r s : Matrix (Fin 3) (Fin 3) C') i j) (D.r_cont i j)
  · intro v i j
    simp only [ht', Matrix.of_apply]
    exact adicCont_av_comp h σ' hinv _ (fun s => (D.t v s : Matrix (Fin 3) (Fin 3) C') i j) (D.t_cont v i j)
  · intro v s i j hij
    rw [ht', Matrix.of_apply, D.t_tri v s i j hij]
    exact av_zero h σ' _
  · intro s a b
    rw [hr', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v a b
    rw [hg', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
  · intro v s a b
    rw [ht', Matrix.of_apply]
    exact av_mem_evp_of_involutive h σ' hinv _ _
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_hasobs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, ∀ j, HasObsG O σ j (coneH2 F.loc (h.ad j) ((B.bar O).bp j)) := by
  intro l _ k _ _ F C₀ hF O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h j
  intro C' _ _ _ p σ' hp hker hσ' hpσ
  obtain ⟨a⟩ := pr_setlift hF O C' R p B hp hker hCont
  obtain ⟨D, hD⟩ := ep_glift O h2 C' R p σ' σ hσ' hpσ B π hGr a
  have hco : ∀ u : ↥(formp σ' (RingHom.ker p) j),
      (∀ x : F.Γ × F.Γ, (D.co u).1 x ∈ adp (ResidueField O) j) ∧
        ∀ (v : F.V) (s : F.Gv v), (D.co u).2 v s ∈ adp (ResidueField O) j :=
    by
      intro u
      have hu' : ∀ i, i ≠ j → ∀ y : RingHom.ker p, (y : C') ∈ evp σ' i → (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) y = 0 := u.2
      have key : ∀ M : Matrix (Fin 3) (Fin 3) C', GrM σ' pq pq M →
          M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O)) ∈ adp (ResidueField O) j := by
        intro M hM
        change ∀ a b, pw a b ≠ j → M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O)) a b = 0
        intro a b hab
        rw [Matrix.map_apply]
        have hmem := hM a b
        rw [← pw_eq] at hmem
        unfold evK
        split_ifs with hk
        · exact hu' (pw a b) hab ⟨M a b, hk⟩ hmem
        · rfl
      obtain ⟨h1, hsub, hmul, hinv, hsgn⟩ := ep_grm σ'
      refine ⟨fun x => ?_, fun v s => ?_⟩
      · refine key (D.om x) ?_
        unfold SetLift.om
        rw [Units.val_mul, Units.val_mul]
        exact hsub _ _ _ _ (hmul _ _ _ _ _ (hmul _ _ _ _ _ (hD.r x.1) (hsgn _ _ (hD.r x.2)))
          (hinv _ _ _ (hD.r (x.1 * x.2)))) (h1 pq)
      · have hX : GrM σ' pq pq ↑((D.g v)⁻¹ * D.t v s * D.g v) := by
          rw [Units.val_mul, Units.val_mul]
          exact hmul _ _ _ _ _ (hmul _ _ _ _ _ (hinv _ _ _ (hD.g v)) (hD.t v s)) (hD.g v)
        refine key (D.a v s) ?_
        unfold SetLift.a
        rw [Units.val_mul]
        exact hsub _ _ _ _ (hmul _ _ _ _ _ (hD.r _) (hinv _ _ _ hX)) (h1 pq)
  have hom := pr_omk hF O C' R p B D hker
  let Ψ : ↥(formp σ' (RingHom.ker p) j) →ₗ[ResidueField O]
      ((F.Γ × F.Γ → ↥(adp (ResidueField O) j)) × ((v : F.V) → F.Gv v → ↥(adp (ResidueField O) j))) :=
    { toFun := fun u => (fun x => ⟨(D.co u).1 x, (hco u).1 x⟩, fun v s => ⟨(D.co u).2 v s, (hco u).2 v s⟩)
      map_add' := by
        intro u w
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_add (f := _)]
      map_smul' := by
        intro c u
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_smul] }
  have hmem : ∀ u, Ψ u ∈ continuousCocycles2 F.loc (h.ad j) ((Box.bar O B).bp j) := by
    intro u
    have k1 : Subtype.val ∘ (Ψ u).1 = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.om := rfl
    have k2 : ∀ v, Subtype.val ∘ (Ψ u).2 v = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.a v := fun v => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k1]
      exact hom.2.2.1.comp _
    · intro v
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k2 v]
      exact (hom.2.2.2 v).comp _
    · intro s t r
      apply Subtype.ext
      exact borelProjection_isTwoCocycle hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker s t r
    · intro v s t
      exact pr_cocv hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker v s t
  refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ Ψ hmem), ?_⟩
  intro u hu C'' _ _ _ q p'' hcomp hq hy
  refine pr_obs hF O R ρ B hU hOf hCont hGood C' p D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker ?_
    C'' q p'' hcomp hq hy
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
  obtain ⟨β, Y, hβ, h1, h3⟩ := hu
  refine ⟨fun g => (β g : Matrix (Fin 3) (Fin 3) (ResidueField O)),
    fun v => (Y v : Matrix (Fin 3) (Fin 3) (ResidueField O)), hβ.comp _, ?_, ?_⟩
  · funext x
    exact congrArg (fun f => (f x : Matrix (Fin 3) (Fin 3) (ResidueField O))) h1
  · intro v s
    exact h3 v s

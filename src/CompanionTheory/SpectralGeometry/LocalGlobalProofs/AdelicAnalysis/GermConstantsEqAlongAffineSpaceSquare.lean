module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourier

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermConstantsEqAlongAffineSpaceSquare
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QuasiRefl

open HeckeCharacterZeroLocus.SiegelWeilU

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}

theorem hform_eq_dot (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem comp_mulVec' (P : Matrix n n A) (x : n → A) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]

theorem hform_mulVec' (P Q : Matrix n n A) (x y : n → A) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (_ᵀ), vecMul_transpose]

theorem hform_sub_left (x d y : n → A) (c : A) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]

theorem hform_sub_right (x d y : n → A) (c : A) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]

theorem hform_smul_right' (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]

theorem hform_conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : n → A) :
    σ (hform σ J x y) = hform σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Form

section Refl

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
  {J : Matrix n n A}

def qrMat (σ : A →+* A) (J : Matrix n n A) (d : n → A) (c : A) : Matrix n n A :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)

theorem qrMat_mulVec (d : n → A) (c : A) (z : n → A) :
    qrMat σ J d c *ᵥ z = z - (c * hform σ J d z) • d := by
  rw [qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]

theorem ext_mulVec' {P Q : Matrix n n A} (h : ∀ z, P *ᵥ z = Q *ᵥ z) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

theorem qrMat_mul (d : n → A) {c c' : A} (hc : c + c' = c * c' * hform σ J d d) :
    qrMat σ J d c * qrMat σ J d c' = 1 := ext_mulVec' fun z => by
  rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d z * d i) * hc

theorem hform_single' (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq_dot, this]
  simp

theorem qrMat_isometry (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) :
    cT σ (qrMat σ J d c) * J * qrMat σ J d c = J := by
  ext i j
  rw [← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec,
    hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ,
    hform_single']
  linear_combination
    (-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc

def qr (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨qrMat σ J d c, qrMat σ J d (σ c), qrMat_mul d hc,
    qrMat_mul d (by linear_combination hc)⟩, qrMat_isometry hσ hJ d c hc⟩

end Refl

theorem exists_unitary_carry (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by
  obtain ⟨bi, hb⟩ := hβ.exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set β := hform σ J x x with hβdef
  set w := hform σ J y x with hw
  have hyy : hform σ J y y = β := hxy.symm
  have hxyw : hform σ J x y = σ w := by rw [hw, hform_conj_symm hσ hJ]
  have hσβ : σ β = β := hform_conj_symm hσ hJ x x
  have hσε : σ (σ ε) = ε := hσ ε
  have hσb : σ bi = bi := by
    have h1 : β * σ bi = 1 := by
      have := congrArg σ hb
      rwa [map_mul, hσβ, map_one] at this
    linear_combination bi * h1 - σ bi * hb
  have hσui : (β - ε * σ w) * σ ui = 1 := by
    have := congrArg σ hui
    rwa [map_mul, map_sub, map_mul, hσβ, hσε, map_one] at this
  set d : Fin M → A := x - ε • y with hd
  have hdx : hform σ J d x = β - σ ε * w := hform_sub_left x y x ε
  have hdy : hform σ J d y = σ w - σ ε * β := by
    rw [hd, hform_sub_left, hxyw, hyy]
  have hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β := by
    rw [hform_sub_right, hdx, hdy]
    ring
  have hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi)
      = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y := by
    rw [map_mul, map_sub, map_one, hσε, hσb, hyy]
    linear_combination (-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε
  have hc₂ : ui + σ ui = ui * σ ui * hform σ J d d := by
    rw [hdd, hε]
    linear_combination (-σ ui) * hui + (-ui) * hσui
  refine ⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩
  · have h2 : qrMat σ J d ui *ᵥ x = ε • y := by
      rw [qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]
      simp
    have h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y := by
      rw [qrMat_mulVec, hform_smul_right', hyy]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y
    rw [← mulVec_mulVec, h2, h3]
  · intro z hxz hyz
    have hdz : hform σ J d z = 0 := by
      rw [hd, hform_sub_left, hxz, hyz]
      simp
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z
    have h2 : qrMat σ J d ui *ᵥ z = z := by
      rw [qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]
    rw [← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]

end GlobalTheory.CompanionTheory.SW.QuasiRefl
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnit
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnit
open Matrix HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.SW.UnitRep

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single_single (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem hform_self_fixed (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (J : Matrix n n A)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : n → A) : σ (hform σ J x x) = hform σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

theorem hform_self_congr (σ : A →+* A) (J : Matrix n n A) (P : Ideal A) (x z : n → A)
    (h₁ : ∀ i, z i - x i ∈ P) (h₂ : ∀ i, σ (z i - x i) ∈ P) :
    hform σ J z z - hform σ J x x ∈ P := by
  have e₁ : ∀ i, Ideal.Quotient.mk P (z i) = Ideal.Quotient.mk P (x i) := fun i =>
    Ideal.Quotient.eq.2 (h₁ i)
  have e₂ : ∀ i, Ideal.Quotient.mk P (σ (z i)) = Ideal.Quotient.mk P (σ (x i)) := fun i =>
    Ideal.Quotient.eq.2 (by simpa only [map_sub] using h₂ i)
  refine Ideal.Quotient.eq.1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, e₁, e₂]

theorem exists_hform_not_mem (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A))
    (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hdet : IsUnit J.det) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ y, hform σ J y y ∉ P := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδu, hδσ⟩ := hδ
  have hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P := fun x y => by
    have h := hcon (x + y)
    rw [hform_add_left, hform_add_right, hform_add_right] at h
    have h' := P.sub_mem (P.sub_mem h (hcon x)) (hcon y)
    convert h' using 1
    ring
  have hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P := fun x y => by
    have h := hpol x (δ • y)
    rw [hform_smul_right', hform_smul_left', hδσ] at h
    convert h using 1
    ring
  have hall : ∀ x y, hform σ J x y ∈ P := fun x y => by
    have h₁ : hform σ J x y - hform σ J y x ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)
    have h₂ : 2 * hform σ J x y ∈ P := by
      convert P.add_mem (hpol x y) h₁ using 1
      ring
    exact (Ideal.unit_mul_mem_iff_mem P h2).1 h₂
  have hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0 := by
    ext i j
    have h := hall (Pi.single i 1) (Pi.single j 1)
    rw [hform_single_single] at h
    simpa using Ideal.Quotient.eq_zero_iff_mem.2 h
  have hd : J.det ∈ P := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_det, hJ0, Matrix.det_zero]
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)

theorem comap_isMaximal (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (P : Ideal A) (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (fun y => ⟨σ y, hσ y⟩)

theorem isCoprime_of_mem_not_mem {P Q : Ideal A} (hP : P.IsMaximal) (hQ : Q.IsMaximal) {a : A}
    (ha : a ∈ P) (ha' : a ∉ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  refine hP.coprime_of_ne hQ ?_
  rintro rfl
  exact ha' ha

theorem exists_good_on_finset [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T _ ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxq : hform σ J x x ∈ q.asIdeal
    swap
    · refine ⟨x, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hxq
      · exact hx p hp
    obtain ⟨y, hy⟩ := exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal
    have hfix := hform_self_fixed σ hσ J hJ x
    have hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ := fun h => by
      rw [Ideal.mem_comap, hfix]; exact h
    have hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ := fun h h' => by
      rw [Ideal.mem_comap, hfix] at h'; exact h h'
    have hqm := q.isMaximal
    have hqc := comap_isMaximal σ hσ q.asIdeal q.isMaximal
    have hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q →
        IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q := fun hQ hn =>
      IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn)
        (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)
    have hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal) :=
      Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)
    have hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ) :=
      Ideal.isCoprime_biInf fun p hp =>
        hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))
    obtain ⟨u, hu, c, hc, huc⟩ := Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)
    have hc₁ : ∀ p ∈ T, c ∈ p.asIdeal := fun p hp =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp
    have hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal := fun p hp =>
      Ideal.mem_comap.1 ((Submodule.mem_iInf _).1
        ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)
    have hu₁ : u ∈ q.asIdeal := Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)
    have hu₂ : σ u ∈ q.asIdeal := Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))
    refine ⟨u • x + c • y, fun p hp => ?_⟩
    have hu' : u = 1 - c := by rw [← huc]; ring
    rcases Finset.mem_insert.1 hp with rfl | hp
    · intro hz
      refine hy ?_
      have h := hform_self_congr σ J p.asIdeal y (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ hu₁
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ hu₂
    · intro hz
      refine hx p hp ?_
      have h := hform_self_congr σ J p.asIdeal x (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ (hc₁ p hp)
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ (hc₂ p hp)

theorem exists_isUnit_hform : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A),
    (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) →
    ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) →
    IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  intro A _ _ σ hσ h2 hδ m J hJ hdet
  have := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨x, hx⟩ := exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ
  refine ⟨x, ?_⟩
  by_contra hnu
  obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  exact hx ⟨P, hP⟩ (Finset.mem_univ _) hmem

end GlobalTheory.CompanionTheory.SW.UnitRep
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnitStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_unit_form_represents_unit : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) → ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform | exact GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform | (intros; apply GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq (InfinitePlace F)]

theorem det_EM_sq {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) :
    (EM ρ (fun v => b v)).det ^ 2 = (discr F : ℝ) := by
  let B : Module.Basis (InfinitePlace F) ℚ F := b.localizationLocalization ℚ ℤ⁰ F
  have hB : ∀ i, B i = (b i : F) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ ℤ⁰ F b i
  have hd : Algebra.discr ℚ B = (discr F : ℚ) := by
    rw [← NumberField.discr_eq_discr F b]
    exact (Algebra.discr_localizationLocalization ℤ ℤ⁰ F b).trans (by simp)
  have hm : (EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v) =
      (algebraMap ℚ ℝ).mapMatrix (Algebra.traceMatrix ℚ B) := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.transpose_apply, EM, RingHom.mapMatrix_apply,
      Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hB]
    simp_rw [← map_mul]
    rw [sum_rho_eq_trace hT hρ]
    simp
  have h2 : (EM ρ (fun v => b v)).det ^ 2 =
      ((EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v)).det := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [h2, hm, ← RingHom.map_det, ← Algebra.discr_def, hd]
  simp

theorem abs_det_gM {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) :
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  have hfr : Module.finrank ℚ F = Fintype.card (InfinitePlace F) :=
    Module.finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ F)
  have hE : |(EM ρ (fun v => b v)).det| = Real.sqrt |(discr F : ℝ)| := by
    rw [← det_EM_sq hT hρ b, abs_of_nonneg (sq_nonneg (EM ρ (fun v => b v)).det), Real.sqrt_sq_eq_abs]
  rw [gM, Matrix.det_smul, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul,
    Fintype.card_prod, abs_mul, abs_pow, abs_pow, hE, hfr, Nat.abs_cast]
  ring

theorem abs_det_gM_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F →
    (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ),
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι :=
  fun _ _ _ _ _ _ _ _ hT hρ b N => abs_det_gM hT hρ b N

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_matrix_determinant_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F → (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), |(gM (ι := ι) ρ (fun v => b v) N).det| = ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | exact GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianFourierTransformFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianFourierTransformFormula
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat

def swapCurry (α β : Type) : (α × β → ℝ) ≃ᵐ (β → α → ℝ) where
  toFun x := fun b a => x (a, b)
  invFun z := fun p => z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun a => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)

theorem swapCurry_measurePreserving (α β : Type) [Fintype α] [Fintype β] :
    MeasurePreserving (swapCurry α β) volume volume := by
  have h : (volume : Measure (α × β → ℝ)) =
      (volume : Measure (β → α → ℝ)).map (swapCurry α β).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (swapCurry α β).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun b => Set.univ.pi (fun a => s (a, b))) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H b a => H (a, b), fun H p => H p.2 p.1⟩
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type_right]
  refine ⟨(swapCurry α β).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integral_cur (f : (InfinitePlace F → ι → ℝ) → ℂ) :
    ∫ x : ι × InfinitePlace F → ℝ, f (cur x) = ∫ z, f z :=
  (swapCurry_measurePreserving ι (InfinitePlace F)).integral_comp' f

theorem dot_DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x y : ι × InfinitePlace F → ℝ) :
    x ⬝ᵥ (DM B ρ *ᵥ y) = ∑ w, cur x w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) := by
  have h : ∀ i w, (DM B ρ *ᵥ y) (i, w) = (B.map (ρ w) *ᵥ cur y w) i := by
    intro i w
    simp only [mulVec, dotProduct, DM, Fintype.sum_prod_type_right, blockDiagonal_apply, cur]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [hv.symm]
    · simp
  rw [dotProduct, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, h, cur]

theorem gauss_fourier_flat : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  intro F _ _ ι _ _ _ M B ρ P hQ τ hτ y
  have h := (GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P hQ τ hτ).2.2.2 (cur y)
  rw [← h, ← integral_cur (F := F) (ι := ι) (fun z => gauss B ρ P τ z *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, z w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) : ℝ) : ℂ)))]
  simp only [dot_DM]

end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianFourierTransformFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_fourier_transform_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | exact GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMatrixSymmetricPosdefImag
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMatrixSymmetricPosdefImag
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem dotProduct_blockDiagonal_mulVec {R ι W : Type} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (f : W → Matrix ι ι R) (y : ι × W → R) :
    y ⬝ᵥ (blockDiagonal f *ᵥ y) = ∑ w, (fun i => y (i, w)) ⬝ᵥ (f w *ᵥ fun i => y (i, w)) := by
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single w]
  · simp [blockDiagonal_apply]
  · intro v _ hv
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [blockDiagonal_apply, hv.symm]
  · simp

theorem dotProduct_block_ofReal {ι : Type} [Fintype ι] (a b : ℝ) (C P : Matrix ι ι ℝ)
    (y : ι → ℝ) :
    (fun i => (y i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => (a : ℂ) * ((C i j : ℝ) : ℂ) +
          Complex.I * (b : ℂ) * ((P i j : ℝ) : ℂ)) *ᵥ fun i => (y i : ℂ)) =
      (a : ℂ) * ((y ⬝ᵥ (C *ᵥ y) : ℝ) : ℂ) + Complex.I * (b : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def ZB {F : Type} [Field F] {ι : Type} {W : Type} (B : Matrix ι ι F) (ρ : W → (F →+* ℝ))
    (P : W → Matrix ι ι ℝ) (τ : W → ℂ) (w : W) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

theorem ZM_eq_blockDiagonal {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := rfl

theorem ZM_map_im {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    (ZM B ρ P τ).map Complex.im = blockDiagonal fun w => (τ w).im • P w := by
  rw [ZM_eq_blockDiagonal]
  ext ⟨i, v⟩ ⟨j, u⟩
  by_cases h : v = u
  · subst h
    simp [ZB, blockDiagonal_apply]
  · simp [ZB, blockDiagonal_apply, h]

theorem ZM_symm_posDef_gauss (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) :
    QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧
        ∀ x : ι × InfinitePlace F → ℝ,
          Complex.exp ((Real.pi : ℂ) * Complex.I *
            ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) =
              gauss B ρ P τ (cur x) := by
  rintro ⟨-, -, hB, -, -, hP, -⟩ τ hτ
  have hPs : ∀ w i j, P w j i = P w i j := fun w i j => by
    simpa using (hP w).isHermitian.apply i j
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [Matrix.IsSymm, ZM_eq_blockDiagonal, blockDiagonal_transpose]
    congr 1
    funext w
    ext i j
    simp only [transpose_apply, ZB, Matrix.of_apply]
    rw [hB.apply i j, hPs w i j]
  · rw [ZM_map_im]
    have hq : ∀ w (y : ι → ℝ), y ≠ 0 → 0 < y ⬝ᵥ (P w *ᵥ y) := fun w y hy => by
      simpa using (hP w).dotProduct_mulVec_pos hy
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext ⟨i, v⟩ ⟨j, u⟩
      by_cases h : v = u
      · subst h
        simp [blockDiagonal_apply, hPs v i j]
      · have h' : ¬ u = v := fun e => h e.symm
        simp [blockDiagonal_apply, h, h']
    · obtain ⟨⟨i, w⟩, hiw⟩ := Function.ne_iff.1 hx
      have hstar : star x = x := by
        funext p
        simp
      rw [hstar, dotProduct_blockDiagonal_mulVec]
      have hterm : ∀ v, (fun i => x (i, v)) ⬝ᵥ (((τ v).im • P v) *ᵥ fun i => x (i, v)) =
          (τ v).im * ((fun i => x (i, v)) ⬝ᵥ (P v *ᵥ fun i => x (i, v))) := fun v => by
        simp [smul_mulVec, dotProduct_smul]
      simp only [hterm]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
      · by_cases hy : (fun i => x (i, v)) = 0
        · simp [hy]
        · exact (mul_pos (hτ v) (hq v _ hy)).le
      · refine mul_pos (hτ w) (hq w _ fun h0 => hiw ?_)
        simpa using congrFun h0 i
  · unfold gauss
    congr 1
    rw [ZM_eq_blockDiagonal, dotProduct_blockDiagonal_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := dotProduct_block_ofReal (τ w).re (τ w).im (B.map (ρ w)) (P w) (cur x w)
    simp only [Matrix.map_apply] at h
    have h2 : (fun i => ((x (i, w) : ℝ) : ℂ)) = fun i => ((cur x w i : ℝ) : ℂ) := rfl
    have h3 : ZB B ρ P τ w = Matrix.of fun i j => ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) +
        Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ) := rfl
    rw [h2, h3, h]
    linear_combination ((Real.pi : ℂ) * ((τ w).im : ℂ) * ((cur x w ⬝ᵥ (P w *ᵥ cur x w) : ℝ) : ℂ)) *
      Complex.I_mul_I

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMatrixSymmetricPosdefImagStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_matrix_symmetric_posdef_imag : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧ ∀ x : ι × InfinitePlace F → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) = gauss B ρ P τ (cur x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | exact GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss <;> assumption)
end
end

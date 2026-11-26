module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.Exchange

section Algebra
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem rowE_mul_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((rowE c p u).val * M) (Sum.inl r) s = M (Sum.inl r) s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem rowE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((rowE c p u).val * M) (Sum.inr r) s =
      M (Sum.inr r) s + if r.val + 1 = p then ∑ t, u t * M (Sum.inl t) s else 0 := by
  by_cases h : r.val + 1 = p <;>
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem mul_rowE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (rowE c p u).val) r (Sum.inr s) = M r (Sum.inr s) := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_rowE_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (rowE c (P.val + 1) u).val) r (Sum.inl s) = M r (Sum.inl s) + M r (Sum.inr P) * u s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem colE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((colE c p u).val * M) (Sum.inr r) s = M (Sum.inr r) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem colE_mul_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((colE c (P.val + 1) u).val * M) (Sum.inl r) s = M (Sum.inl r) s + u r * M (Sum.inr P) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem mul_colE_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (colE c p u).val) r (Sum.inl s) = M r (Sum.inl s) := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_colE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (colE c p u).val) r (Sum.inr s) =
      M r (Sum.inr s) + if s.val + 1 = p then ∑ t, M r (Sum.inl t) * u t else 0 := by
  by_cases h : s.val + 1 = p <;>
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem rowE_neg_mul (p : ℕ) (u : n → k) : rowE c p (-u) * rowE c p u = 1 := by
  ext1
  simp only [rowE, lowU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h]

theorem colE_neg_mul (p : ℕ) (u : n → k) : colE c p (-u) * colE c p u = 1 := by
  ext1
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : s.val + 1 = p <;> simp [h]

theorem rowE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    rowE c p u * embX c g = embX c g * rowE c p (g.valᵀ.mulVec u) := by
  ext1
  simp only [rowE, lowU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
    fromBlocks_multiply]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

theorem colE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    colE c p u * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
  have : colE c p (g.val.mulVec ((g⁻¹).val.mulVec u)) * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
    generalize (g⁻¹).val.mulVec u = w
    ext1
    simp only [colE, upU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_multiply]
    congr 1 <;> simp
    ext l s; by_cases h : s.val + 1 = p <;> simp [h, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem rowE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (P.val + 1 + 1)) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      rowE c (P.val + 1) u * g = h * rowE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val ≤ P.val + 1 → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simpa [lev] using h)
  have h21 : ∀ (r : Fin c) s, P.val < r.val → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simp [lev]; omega)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inr P) (Sum.inl s), fun u => ⟨rowE c (P.val + 1) u * g *
    rowE c (P.val + 1) (-(u + fun s => g.val (Sum.inr P) (Sum.inl s))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_rowE_inl, mul_rowE_inr, rowE_mul_inl, rowE_mul_inr]
    · simp [h11, h12 r P (by omega), Matrix.one_apply]
    · simp [h12 r s (by omega)]
    · by_cases hr : r = P
      · subst hr; simp [h11, h12, h22]; ring
      · have : P.val < r.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h21 r s this, h22 r P this.le, hr, this.ne']
    · by_cases hr : r = P
      · subst hr; simp [h22 r s (by omega), fun t => h12 t s (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_rowE_inr, rowE_mul_inr]
      split_ifs with hi
      · simp [fun t => h12 t j (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, rowE_neg_mul, mul_one]

theorem colE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c P.val) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      colE c (P.val + 1) u * g = h * colE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val < P.val → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simp [lev]; omega)
  have h21 : ∀ (r : Fin c) s, P.val ≤ r.val + 1 → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simpa [lev] using h)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inl s) (Sum.inr P), fun u => ⟨colE c (P.val + 1) u * g *
    colE c (P.val + 1) (-(u + fun s => g.val (Sum.inl s) (Sum.inr P))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_colE_inl, mul_colE_inr, colE_mul_inl, colE_mul_inr]
    · simp [h11, h21 P s (by omega), Matrix.one_apply]
    · by_cases hr : s = P
      · subst hr; simp [h11, h21, h22]; ring
      · have : s.val < P.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h12 r s this, h22 P s this.le, Ne.symm hr, this.ne]
    · simp [h21 r s (by omega)]
    · by_cases hr : s = P
      · subst hr; simp [h22 r s (by omega), fun t => h21 r t (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_colE_inr, colE_mul_inr]
      split_ifs with hi
      · simp [fun t => h21 i t (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, colE_neg_mul, mul_one]

end Algebra

section Analysis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]

theorem integrable_of_mem_SB {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2

def avg (T : (n → k) → A →ₗ[ℂ] A) (l : A →ₗ[ℂ] ℂ) (h : ∀ v, (fun u => l (T u v)) ∈ SB (n → k)) :
    A →ₗ[ℂ] ℂ where
  toFun v := ∫ u, l (T u v) ∂(Measure.pi fun _ => ν)
  map_add' v w := by
    simp only [map_add (f := _)]
    exact integral_add (integrable_of_mem_SB ν (h v)) (integrable_of_mem_SB ν (h w))
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul a _

def avg₂ {P : Type} [AddCommGroup P] [Module ℂ P] (T : (n → k) → A →ₗ[ℂ] A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (h : ∀ φ v, (fun u => b φ (T u v)) ∈ SB (n → k)) : P →ₗ[ℂ] A →ₗ[ℂ] ℂ where
  toFun φ := avg ν T (b φ) (h φ)
  map_add' φ φ' := by
    ext v
    simp only [avg, map_add (f := _), LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact integral_add (integrable_of_mem_SB ν (h φ v)) (integrable_of_mem_SB ν (h φ' v))
  map_smul' a φ := by
    ext v
    simp only [avg, map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    exact integral_smul a _

theorem isNEquiv_integral {ψ : AddChar k Circle} {p q : ℕ} {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {l : A → ℂ} (hl : IsNEquiv ψ p σ l) (E : (n → k) → GL (n ⊕ Fin c) k)
    (hE : ∀ g ∈ N k n c q, ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c p, simpleSum h = simpleSum g ∧
      E u * g = h * E (u + w)) :
    IsNEquiv ψ q σ fun v => ∫ u, l (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  intro g hg v
  obtain ⟨w, hw⟩ := hE g hg
  have : ∀ u, l (σ (E u) (σ g v)) = (ψ (simpleSum g) : ℂ) * l (σ (E (u + w)) v) := fun u => by
    obtain ⟨h, hN, hs, he⟩ := hw u
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hl h hN, hs]
  simp only [this]
  rw [integral_const_mul, integral_add_right_eq_self (fun u => l (σ (E u) v)) w]

theorem integral_embX {P : Type} [AddCommGroup P] [Module ℂ P] {π : Representation ℂ (GL n k) P}
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (E : (n → k) → GL (n ⊕ Fin c) k)
    (g m : GL n k) (z : ℝ) (φ : P) (hb : ∀ v, b (π g φ) (σ (embX c g) v) = (z : ℂ) * b φ v)
    (hE : ∀ u, E u * embX c g = embX c g * E (m.val.mulVec u)) (v : A) :
    ∫ u, b (π g φ) (σ (E u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      ((z * (nabs k (Matrix.GeneralLinearGroup.det m))⁻¹ : ℝ) : ℂ) *
        ∫ u, b φ (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  have : ∀ u, b (π g φ) (σ (E u) (σ (embX c g) v)) = (z : ℂ) * b φ (σ (E (m.val.mulVec u)) v) := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, hE, map_mul, Module.End.mul_apply, hb]
  simp only [this]
  rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m (fun u => b φ (σ (E u) v))]
  simp [mul_assoc]

end Analysis

theorem exchange_isPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exUp ν p σ l v) ∧ IsNEquiv ψ (p + 1) σ l') ∧ (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (p + 1) σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exDown ν p σ l v) ∧ IsNEquiv ψ p σ l') ∧ ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (IsPos ψ p π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exUp ν p σ (b φ) v) ∧ IsPos ψ (p + 1) π σ b') ∧ (IsPos ψ (p + 1) π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exDown ν p σ (b φ) v) ∧ IsPos ψ p π σ b') := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have up : ∀ l : A → ℂ, IsNEquiv ψ p σ l → IsNEquiv ψ (p + 1) σ (exUp ν p σ l) := fun l hl => by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact isNEquiv_integral ν hl _ fun g hg => rowE_mul_mem ⟨q, by omega⟩ hg
  have down : ∀ l : A → ℂ, IsNEquiv ψ (p + 1) σ l → IsNEquiv ψ p σ (exDown ν p σ l) := fun l hl =>
    isNEquiv_integral ν hl _ fun g hg => colE_mul_mem ⟨p, hpc⟩ hg
  refine ⟨fun l hl => ⟨avg ν (fun u => σ (rowE c p u)) l fun v => ((H l v).1 hl).1, fun v => rfl, up l hl⟩,
    fun l hl => ⟨avg ν (fun u => σ (colE c (p + 1) u)) l fun v => ((H l v).2 hl).1, fun v => rfl, down l hl⟩,
    fun P _ _ π b => ⟨fun hb => ⟨avg₂ ν (fun u => σ (rowE c p u)) b fun φ v => ((H (b φ) v).1 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => up _ (hb.1 φ), fun g φ v => ?_⟩,
    fun hb => ⟨avg₂ ν (fun u => σ (colE c (p + 1) u)) b fun φ v => ((H (b φ) v).2 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => down _ (hb.1 φ), fun g φ v => ?_⟩⟩⟩
  · let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    refine (integral_embX ν (rowE c p) g m _ φ (hb.2 g φ) (fun u => rowE_mul_embX p u g) v).trans ?_
    rw [hm, ← Real.rpow_neg_one, ← Real.rpow_add (nabs_pos k _)]
    congr 3
    push_cast; ring
  · refine (integral_embX ν (colE c (p + 1)) g g⁻¹ _ φ (hb.2 g φ) (fun u => colE_mul_embX (p + 1) u g) v).trans ?_
    have hm : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← nabs_mul, ← map_mul, inv_mul_cancel, map_one, nabs_one]
    rw [hm, ← Real.rpow_add_one (nabs_pos k _).ne']
    congr 3
    push_cast; ring

end GlobalTheory.RootEx.Exchange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem rowE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    rowE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hC : (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) = 0 := by
    ext l s
    simp
  show Matrix.fromBlocks 1 0
      (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) 1 = 1
  rw [hC, Matrix.fromBlocks_one]

theorem colE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    colE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hB : (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) = 0 := by
    ext r i
    simp
  show Matrix.fromBlocks 1
      (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) 0 1 = 1
  rw [hB, Matrix.fromBlocks_one]

private theorem sigmaCompactSpace_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
  have hδ : (1 : ValueGroupWithZero k) < γ⁻¹ := one_lt_inv_iff₀.mpr ⟨hγ0, hγ1⟩
  refine ⟨⟨fun m : ℕ => {x : k | valuation k x ≤ γ⁻¹ ^ m},
    fun m => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact MulArchimedean.arch (valuation k x) hδ

private theorem fourier_fourier_eq_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    [DecidableEq n] (ψ : AddChar k Circle) (ν : Measure k) [SigmaFinite ν] [ν.IsAddHaarMeasure]
    (hF : ∀ f ∈ SB (n → k), ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0)
    (f : (n → k) → ℂ) (hf : f ∈ SB (n → k)) (z : n → k) :
    ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ z) : ℂ)
      ∂(Measure.pi fun _ => ν) = f (-z) := by
  have hτ : (fun x : n → k => f (x - z)) ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_sub_right z), hf.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have key : ∀ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
      * (ψ (y ⬝ᵥ z) : ℂ) = ∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro y
    rw [← integral_mul_const,
      ← integral_add_right_eq_self (fun x : n → k => f (x - z) * (ψ (x ⬝ᵥ y) : ℂ)) z]
    congr 1
    funext x
    simp only [add_sub_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul,
      dotProduct_comm z y]
    ring
  calc _ = ∫ y : n → k, (∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) := by
          congr 1
          funext y
          exact key y
    _ = f (0 - z) := hF _ hτ
    _ = f (-z) := by rw [zero_sub]

theorem exDown_exUp_and_exUp_exDown : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → exDown ν p σ (exUp ν p σ l) v = l v) ∧ (IsNEquiv ψ (p + 1) σ l → exUp ν p σ (exDown ν p σ l) v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψc hψ1 ν hsd A _ _ σ hσ l v
  have : ν.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.rootExchange_support_and_fourier_relation k n c p hp hpc ψ hψc hψ1 ν A σ hσ l v
  have hF := GlobalTheory.T.fourier_transform_inversion_localFieldPi k n ψ hψc hψ1 ν hsd
  constructor
  · intro hN
    obtain ⟨hSB, -, hint⟩ := hT.1 hN
    have h1 : exDown ν p σ (exUp ν p σ l) v
        = ∫ β : n → k, ∫ u : n → k, (fun u : n → k => l (σ (rowE c p u) v)) u * (ψ (u ⬝ᵥ β) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exDown
      congr 1
      funext β
      rw [hint β]
      congr 1
      funext u
      ring
    rw [h1, (hF _ hSB).2]
    simp [rowE_zero_eq_one]
  · intro hN
    obtain ⟨hSB, hcomm⟩ := hT.2 hN
    have : SigmaCompactSpace k := sigmaCompactSpace_nonarchimedeanLocalField k
    have : SigmaFinite ν := inferInstance
    have hF2 := fun f hf => (hF f hf).2
    have hG := (hF _ hSB).1
    have hGG := (hF _ hG).1
    have h1 : exUp ν p σ (exDown ν p σ l) v
        = ∫ u : n → k, ∫ y : n → k, (∫ x : n → k, (∫ β : n → k, l (σ (colE c (p + 1) β) v)
            * (ψ (β ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (x ⬝ᵥ y) : ℂ)
            ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ u) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exUp exDown
      congr 1
      funext u
      rw [fourier_fourier_eq_neg ψ ν hF2 _ hG u]
      congr 1
      funext β
      rw [hcomm u β, dotProduct_neg, dotProduct_comm]
      ring
    rw [h1, hF2 _ hGG]
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    rw [hF2 _ hSB]
    show l (σ (colE c (p + 1) 0) v) = l v
    rw [colE_zero_eq_one, map_one]
    rfl

end GlobalTheory.RootEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.TargetUnip

theorem det_eq_one_of_level {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hb : M.BlockTriangular f := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock f a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM _ _ (by rw [i.2, j.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']

theorem mul_apply_of_inN {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) {m : Type*}
    (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (h.val * x) r s = x r s + ∑ r', if lev p r < lev p r' then h.val r r' * x r' s else 0 := by
  have h1 : x r s = ∑ r', (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r r' * x r' s := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r' _ => ?_
  split_ifs with hl
  · rw [Matrix.one_apply_ne, zero_mul, zero_add]
    rintro rfl
    exact lt_irrefl _ hl
  · rw [hh r r' (not_lt.1 hl), add_zero]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_of_not_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r s} (hrs : ¬ Free p (r, s)) :
    affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, hrs]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_eq_zero (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r r' : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hrs : ¬ Free p (r, s))
    (hl : lev p r < lev p r') : affPt p x₀ e r' s = 0 := by
  rcases r with r | r <;> rcases r' with r' | r' <;> rcases s with s | s <;>
    simp only [lev, Free, Sum.elim_inl, Sum.elim_inr, lt_irrefl] at hrs hl <;>
    rw [affPt_of_not_free _ _ _ (by simp only [Free]; omega)] <;>
    simp [basePt] <;> omega

open Classical in
def linPart (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

open Classical in
theorem det_linPart {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) :
    (linPart (n' := n') p h.val).det = 1 := by
  refine det_eq_one_of_level (fun a => lev p a.1.1) _ fun a b hab => ?_
  simp only [linPart, Matrix.of_apply]
  rw [hh _ _ hab]
  simp only [Matrix.one_apply, Subtype.ext_iff, Prod.ext_iff]
  by_cases h1 : a.1.1 = b.1.1 <;> by_cases h2 : a.1.2 = b.1.2 <;> simp [h1, h2]

open Classical in
theorem linPart_mulVec (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by
  let F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun b =>
    (if a.1.2 = b.2 then h a.1.1 b.1 else 0) * (if hf : Free p b then e ⟨b, hf⟩ else 0)
  have h1 : (linPart p h).mulVec e a = ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 := by
    simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, F]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dite_eq_left b.2]
  have h2 : ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 = ∑ b, F b := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun b => Free p b) (by simp) F]
    refine Finset.sum_filter_of_ne fun b _ hb => ?_
    by_contra hf
    exact hb (by simp [F, hf])
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single a.1.2]
  · simp [F]
  · intro s _ hs
    simp [F, hs.symm]
  · simp

open Classical in
theorem mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    h.val * affPt p x₀ e = affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases hf : Free p (r, s)
  · have : affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) r s =
        basePt c x₀ r s + ((linPart p h.val).mulVec e ⟨(r, s), hf⟩ +
          (h.val * basePt c x₀ - basePt c x₀) r s) := by
      simp [affPt, hf]
    rw [this, linPart_mulVec, affPt, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    ring
  · rw [affPt_of_not_free _ _ _ hf, mul_apply_of_inN hh, affPt_of_not_free _ _ _ hf,
      Finset.sum_eq_zero, add_zero]
    intro r' _
    split_ifs with hl
    · rw [affPt_eq_zero p x₀ e hf hl, mul_zero]
    · rfl

omit [Fintype n'] [DecidableEq n'] in
theorem ch_mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (h.val * affPt p x₀ e) = ch (affPt p x₀ e) + simpleSum h := by
  rw [ch, ch, simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_of_inN hh, Fintype.sum_sum_type, Finset.sum_eq_zero, zero_add]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : lev (n := n) p (Sum.inr i) < lev (n := n) p (Sum.inr j)
    · rw [if_pos hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rw [if_neg hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [if_neg (by omega)]
  · intro r _
    split_ifs with hl
    · simp only [lev, Sum.elim_inr, Sum.elim_inl] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rfl

end GlobalTheory.RootEx.TargetUnip

open GlobalTheory.RootEx.TargetUnip in
theorem GlobalTheory.RootEx.opE_om_target_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n c p, opE ψ ν p (om μ 1 g Φ) = (ψ (-simpleSum g) : ℂ) • opE ψ ν p Φ := by
  classical
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hg
  obtain ⟨hN, hadd, hdet, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  have hg' : g⁻¹ ∈ N k n c p := inv_mem hg
  have hh : InN p g⁻¹ := (hN _).1 hg'
  have hs1 : simpleSum (1 : GL (n ⊕ Fin c) k) = 0 := by
    have := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_add.1 this
  have hs : simpleSum g⁻¹ = -simpleSum g := by
    have := hadd g hg g⁻¹ hg'
    rw [mul_inv_cancel, hs1] at this
    linear_combination -this
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : ∀ x, om μ 1 g Φ x = Φ ((g⁻¹).val * x) := by
    intro x
    simp [om, hdet g hg, hn1]
  haveI := secondCountable k
  funext x₀
  let F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ := fun e =>
    Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)
  let t : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => ((g⁻¹).val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2
  let L := Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart (n' := n') p (g⁻¹).val)
    (by rw [det_linPart hh]; exact one_ne_zero)
  have hL : Matrix.GeneralLinearGroup.det L = 1 := by
    ext
    exact det_linPart hh
  have key : ∀ e, om μ 1 g Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (-simpleSum g) : ℂ) * F (L.val.mulVec e + t) := by
    intro e
    have h1 := mul_affPt hh x₀ e
    have h2 := ch_mul_affPt hh x₀ e
    have h3 : F (L.val.mulVec e + t) = Φ ((g⁻¹).val * affPt p x₀ e) *
        (ψ (-ch ((g⁻¹).val * affPt p x₀ e)) : ℂ) := by
      rw [h1]; rfl
    rw [h3, h2, hs, hom, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have hcov := integral_comp_mulVec_eq_smul ν L
    (fun e => F (e + t))
  rw [hL, hn1, inv_one, one_smul, integral_add_right_eq_self] at hcov
  simp only [opE, Pi.smul_apply, smul_eq_mul, key]
  rw [integral_const_mul, hcov]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootExSource

theorem det_eq_one_of_unip {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (b : ι → ℕ)
    (M : Matrix ι ι k) (h : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hT : M.BlockTriangular b := fun r s hrs => by
    rw [h r s hrs.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hrs
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext r s
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ (by rw [r.2, s.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_one]

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}

theorem mul_apply_of_inN {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by
  have : x r s = (x * (1 : Matrix (n' ⊕ Fin c) (n' ⊕ Fin c) k)) r s := by rw [Matrix.mul_one]
  rw [this, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne, mul_zero, zero_add]
    rintro rfl
    exact lt_irrefl _ h
  · rw [hg s' s (not_lt.1 h), add_zero]

theorem affPt_nonfree (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, h]

theorem affPt_mul_nonfree {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : (affPt p x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [mul_apply_of_inN hg, affPt_nonfree _ _ _ _ h, Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ Free p (r, s') ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, lev, basePt] at h h' ⊢ <;> omega
    rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
  · rfl

theorem simpleSum_succ (g : GL (n' ⊕ Fin (c + 1)) k) :
    simpleSum g = ∑ l : Fin c, g.val (Sum.inr l.castSucc) (Sum.inr l.succ) := by
  unfold simpleSum
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin (c + 1) =>
    if j.val = (Fin.last c).val + 1 then g.val (Sum.inr (Fin.last c)) (Sum.inr j) else 0), add_zero]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · simp
  · intro j _
    rw [if_neg]
    have := j.2
    simp only [Fin.val_last]
    omega

theorem ch_affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p x₀ e * g.val) = ch (affPt p x₀ e) + simpleSum g := by
  rw [simpleSum_succ, ch, ch, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_apply_of_inN hg, Finset.sum_eq_single (Sum.inr l.castSucc)]
  · rw [if_pos (by simp [lev]), affPt_nonfree _ _ _ (Sum.inr l.castSucc) (by simp [Free])]
    simp [basePt]
  · intro s' _ hs
    split_ifs with h'
    · have : ¬ Free p ((Sum.inr l : n ⊕ Fin c), s') ∧ basePt c x₀ (Sum.inr l) s' = 0 := by
        rcases s' with s' | s' <;> simp [Free, lev, basePt, Fin.ext_iff] at hs h' ⊢ <;> omega
      rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
    · rfl
  · simp

def linPart (n : Type) [DecidableEq n] (p : ℕ) (g : GL (n' ⊕ Fin (c + 1)) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g.val b.1.2 a.1.2 else 0

open Classical in
theorem det_linPart {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by
  rw [← det_transpose]
  refine det_eq_one_of_unip (fun a => lev p a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linPart, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

open Classical in
theorem affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e * g.val = affPt p x₀ ((linPart n p g).mulVec e +
      fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases h : Free p (r, s)
  · have key : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
        ∑ s', (if h : Free p (r, s') then e ⟨(r, s'), h⟩ else 0) * g.val s' s := by
      have h1 : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
          ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), (if b.1 = r then g.val b.2 s else 0) *
            (if h : Free p b then e ⟨b, h⟩ else 0) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free p b)]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ Free p b} => _)
          (fun b _ => by rw [dite_eq_right b.2, mul_zero]), add_zero]
        simp only [Matrix.mulVec, dotProduct, linPart, of_apply]
        refine Finset.sum_congr rfl fun b _ => by rw [dite_eq_left b.2]
      rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro r' _ hr
        simp [hr]
      · simp
    unfold affPt
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, of_apply, dite_eq_left h, Pi.add_apply, key]
    simp only [Matrix.mul_apply, Matrix.sub_apply, of_apply]
    ring
  · rw [affPt_mul_nonfree hg _ _ _ _ h, affPt_nonfree _ _ _ _ h]

private theorem secondCountable_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact secondCountable_of_proper

theorem opE_om_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n' (c + 1) p, opE ψ ν p (om μ g 1 Φ) = (ψ (simpleSum g) : ℂ) • opE ψ ν p Φ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hgN
  classical
  have := secondCountable_local k
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n' (c + 1) p
  have hg : InN p g := (h1 g).1 hgN
  have hdet := h3 g hgN
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : om μ g 1 Φ = fun x => Φ (x * g.val) := by
    funext x
    simp [om, hdet, hn1]
  funext x₀
  rw [hom, Pi.smul_apply, smul_eq_mul]
  unfold opE
  set v : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2 with hv
  set F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) with hF
  let G : GL {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart n p g) (by rw [det_linPart hg]; exact one_ne_zero)
  have hGval : G.val = linPart n p g := rfl
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGval, det_linPart hg]; rfl
  have hcov := (GlobalTheory.SplitWeil.linear_change_of_variables k {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} n ν).1 G
    (fun e => F (e + v))
  rw [hGdet, hn1, inv_one, one_smul, hGval] at hcov
  have hint : ∀ e, Φ (affPt p x₀ e * g.val) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (simpleSum g) : ℂ) * F ((linPart n p g).mulVec e + v) := by
    intro e
    simp only [hF]
    rw [hv, ← affPt_mul hg, ch_affPt_mul hg, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  simp only [hint]
  rw [integral_const_mul, hcov]
  congr 1
  exact integral_add_right_eq_self F v

end GlobalTheory.RootExSource
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (X := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

end GlobalTheory.SBExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.DualAverage

theorem isLocallyConstant_orbit {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} (hσ : IsSmooth σ) (u : W) :
    IsLocallyConstant fun g : G => σ g u := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | σ x u = u}) := (hσ u).preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simp)] with x hx
  have hx' : σ (g⁻¹ * x) u = u := hx
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_invariant_form (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (l₀ : Module.Dual ℂ W) :
    ∃ l : Module.Dual ℂ W, (∀ h ∈ H, ∀ w, l (σ h w) = l w) ∧
      ∀ w, (∀ h ∈ H, σ h w = w) → l w = l₀ w := by
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH
  borelize ↥H
  let η : Measure H := Measure.haar
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  have hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η := by
    intro w
    have hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w) :=
      (((isLocallyConstant_orbit hσ w).comp_continuous
        (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : Module.Dual ℂ W :=
    { toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η
      map_add' := fun v w => by
        simp only [map_add (f := _)]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η := fun _ => rfl
  refine ⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, ha, ha,
      ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]
    congr 2
    funext h
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [LinearMap.smul_apply, ha]
    have : (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w :=
      funext fun h => by rw [hw _ (inv_mem h.2)]
    rw [this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.SmGL.DualAverage
end

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumns
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnity
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LevelLaw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : Type} [Fintype n] [DecidableEq n]

private theorem reGL_mem_KO_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) :
    _root_.GlobalTheory.StepData.reGL e g ∈ _root_.GlobalTheory.SplitWeil.KO k b := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv, _root_.GlobalTheory.StepData.reGL_val, _root_.GlobalTheory.StepData.reGL_val]
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff _).mp hg
  exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

private theorem exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {δ : kˣ →* ℂˣ} (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) {u : kˣ} (hu : valuation k (u : k) = 1) : ∃ n : ℕ, 0 < n ∧ δ u ^ n = 1 := by
  classical
  have hO := Valuation.integer.integers (valuation k)
  let x : 𝒪[k] := ⟨u, by rw [Valuation.mem_integer_iff, hu]⟩
  have hx : IsUnit x := hO.isUnit_iff_valuation_eq_one.mpr hu
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  have hr : IsLocalRing.residue 𝒪[k] x ≠ 0 := (RingHom.isUnit_map _ hx).ne_zero
  have hq : 1 < Fintype.card (IsLocalRing.ResidueField 𝒪[k]) := Fintype.one_lt_card
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1, by omega, ?_⟩
  have hmem : x ^ (Fintype.card (IsLocalRing.ResidueField 𝒪[k]) - 1) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  have hnu := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  have hlt := lt_of_le_of_ne (hO.map_le_one _) (mt hO.isUnit_iff_valuation_eq_one.mpr hnu)
  rw [← map_pow]
  apply hδ
  refine lt_of_eq_of_lt ?_ hlt
  simp [x]
  rfl

private theorem hasTypes_apply_mul_left_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL b k} (hg : g ∈ Q.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k b) (B : Matrix b a k) :
    Φ (g.val * B) = ((Q.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.2 ⟨g⁻¹, inv_mem hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g⁻¹) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO (inv_mem hgi))
  have hl : Q.lam ⟨g⁻¹, inv_mem hg⟩ = (Q.lam ⟨g, hg⟩)⁻¹ := map_inv Q.lam ⟨g, hg⟩
  rw [map_inv] at hn
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_inv, Matrix.mul_one, hl, hn, map_one, Real.one_rpow, Units.val_one, one_mul, map_inv, Units.val_inv_eq_inv_val, Complex.ofReal_one, mul_one, Units.val_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

private theorem hasTypes_apply_mul_right_of_mem_J_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ} {P : _root_.GlobalTheory.StepData.Level (GL a k)} {Q : _root_.GlobalTheory.StepData.Level (GL b k)} {Φ : Matrix b a k → ℂ} (hΦ : _root_.GlobalTheory.StepData.HasTypes μ P Q Φ) {g : GL a k} (hg : g ∈ P.J) (hgi : g ∈ _root_.GlobalTheory.SplitWeil.KO k a) (B : Matrix b a k) :
    Φ (B * g.val) = ((P.lam ⟨g, hg⟩ : ℂ) * ((μ (GeneralLinearGroup.det g) : ℂ))⁻¹) * Φ B := by
  have key := congrFun (hΦ.1 ⟨g, hg⟩) B
  have hn : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hgi)
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, Units.smul_def, inv_one, Matrix.one_mul, hn, map_one, Real.one_rpow, Units.val_one, one_mul, inv_one, Complex.ofReal_one, mul_one, _root_.GlobalTheory.SplitWeil.nabs_one, smul_eq_mul] at key
  rw [mul_right_comm, ← key, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

private theorem withCol_toBlocks11_mul_mulVec_eq_mul_withCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix n n' k) (y : n → k) : _root_.GlobalTheory.StepData.withCol (g.val.toBlocks₁₁ * x) (g.val.toBlocks₁₁ *ᵥ y) = g.val * _root_.GlobalTheory.StepData.withCol x y := by
  ext (i | i) (j | j)
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]
  · simp [_root_.GlobalTheory.StepData.withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, mulVec, dotProduct]
  · exact i.elim0
  · exact i.elim0

private theorem fromCols_zero_mul_toBlocks11_eq_mul_val {k : Type} [Field k] {n m : Type} [Fintype n] [DecidableEq n] (g : GL (n ⊕ Fin 0) k) (x : Matrix (m ⊕ Unit) n k) :
    (x * g.val.toBlocks₁₁).toRows₁.fromCols 0 = x.toRows₁.fromCols 0 * g.val := by
  ext i (j | j)
  · change _ = ∑ l, (x.toRows₁.fromCols (0 : Matrix m (Fin 0) k)) i l * (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) l (Sum.inl j)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, toRows₁, toBlocks₁₁]
  · exact j.elim0

private theorem mul_apply_inr_unit_eq_vecMul {k : Type} [Field k] {n m : Type} [Fintype n] (x : Matrix (m ⊕ Unit) n k) (B : Matrix n n k) :
    (x * B) (Sum.inr ()) = x (Sum.inr ()) ᵥ* B := by
  funext j
  simp [Matrix.mul_apply, vecMul, dotProduct]

private theorem mulVec_mem_box_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) {m : n → k} (hm : m ∈ _root_.GlobalTheory.StepData.box n w) : (G : Matrix n n k) *ᵥ m ∈ _root_.GlobalTheory.StepData.box n w := by
  rw [_root_.GlobalTheory.StepData.mem_box] at hm ⊢
  intro i
  have hGi := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff G).mp hG).1 i
  refine (Valuation.map_sum_le _ fun j _ => ?_)
  rw [map_mul]
  calc valuation k ((G : Matrix n n k) i j) * valuation k (m j) ≤ 1 * valuation k (m j) := by
        gcongr
        exact (Valuation.mem_integer_iff _ _).mp (hGi j)
    _ ≤ valuation k (w : k) := by rw [one_mul]; exact hm j

private theorem hat_cosetInd_box_vecMul_KO_eq_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (ε : k) (G : GL n k) (hG : G ∈ _root_.GlobalTheory.SplitWeil.KO k n) (w : kˣ) (y v : n → k) :
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk y)) (v ᵥ* (G : Matrix n n k)) =
      _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y))) v := by
  have hdet : _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det G) = 1 :=
    _root_.GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hG)
  have hiff : ∀ z : n → k, (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) z = Submodule.Quotient.mk y) ↔
      (Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n w) ((G : Matrix n n k) *ᵥ z) = Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) := by
    intro z
    simp only [Submodule.Quotient.eq, ← mulVec_sub]
    refine ⟨mulVec_mem_box_of_mem_KO G hG w, fun h => ?_⟩
    have := mulVec_mem_box_of_mem_KO G⁻¹ (inv_mem hG) w h
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  unfold _root_.GlobalTheory.StepData.hat
  have h := _root_.GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν G (fun z => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n w) (Submodule.Quotient.mk ((G : Matrix n n k) *ᵥ y)) z * ((ψ (ε * v ⬝ᵥ z) : Circle) : ℂ))
  rw [hdet, inv_one, one_smul] at h
  rw [← h]
  congr 1
  ext z
  rw [dotProduct_mulVec]
  congr 1
  unfold _root_.GlobalTheory.StepData.cosetInd
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← hiff z]

theorem _root_.GlobalTheory.LevelLaw.last_steps_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), _root_.GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : _root_.GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, _root_.GlobalTheory.SplitWeil.IsUnram (η j)) → ∀ g : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : _root_.GlobalTheory.StepData.XIx κ t (s + 1) → k) x, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).xiTop (_root_.GlobalTheory.StepData.box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  intro k _ _ _ _ _ _ ν hν s κ t _ _ _ _ δ hδ η hη g hg
  haveI := hν.1
  set F := _root_.GlobalTheory.StepData.plainFrame (k := k) (_root_.GlobalTheory.StepData.stdOrd κ t (l := s + 1) (s + 1) 0 rfl) with hF
  have hg' : F.conj.symm g ∈ (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).J :=
    _root_.GlobalTheory.StepData.Level.mem_map.mp hg
  have hgg : g = _root_.GlobalTheory.StepData.reGL F.ord (F.conj.symm g) := by
    have := F.conj_apply (F.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    simpa [hF, _root_.GlobalTheory.StepData.plainFrame] using this
  have hlam : ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ =
      (_root_.GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 1) × t) δ hδ).lam ⟨F.conj.symm g, hg'⟩ :=
    _root_.GlobalTheory.StepData.Level.map_lam _ _ _
  obtain ⟨hg'int, hg'low⟩ := _root_.GlobalTheory.StepData.mem_parahoric.mp hg'
  obtain ⟨⟨A, hA, hAeq⟩, ⟨D, -, hDeq⟩⟩ := _root_.GlobalTheory.StepData.exists_diag_blocks hg'int hg'low
  have hint : g ∈ _root_.GlobalTheory.SplitWeil.KO k _ := by
    rw [hgg]
    exact reGL_mem_KO_of_mem_KO _ hg'int
  have hdet : GeneralLinearGroup.det g = GeneralLinearGroup.det (F.conj.symm g) := by
    conv_lhs => rw [hgg]
    exact _root_.GlobalTheory.StepData.det_reGL _ _
  have hsplit := _root_.GlobalTheory.StepData.tame_det_blocks hδ hg'int hg'low hAeq hDeq
  have hval := _root_.GlobalTheory.StepData.valuation_det_of_mem_KO hint
  set c : ℂˣ := ((_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).lam ⟨g, hg⟩ *
    (δ (GeneralLinearGroup.det g))⁻¹ with hc
  have hcA : c = (δ (GeneralLinearGroup.det A))⁻¹ := by
    rw [hc, hlam, _root_.GlobalTheory.StepData.parahoric_lam _ D hDeq, hdet, hsplit, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hroot : ∃ n : ℕ, 0 < n ∧ (c : ℂ) ^ n = 1 := by
    obtain ⟨n, hn, hpow⟩ := exists_pos_pow_eq_one_of_isTame_of_valuation_eq_one hδ (_root_.GlobalTheory.StepData.valuation_det_of_mem_KO hA)
    exact ⟨n, hn, by rw [← Units.val_pow_eq_pow_val, hcA, inv_pow, hpow, inv_one, Units.val_one]⟩
  have hL := _root_.GlobalTheory.StepData.Chain.ofTwist_laws δ hδ η hη
    (fun j c h ↦ _root_.GlobalTheory.StepData.plainFrame (_root_.GlobalTheory.StepData.stdOrd κ t j c h))
    (_root_.GlobalTheory.StepData.LatFrame.refl k (_root_.GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) t (s + 2)))
  have hmu : ∀ j, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu j (GeneralLinearGroup.det g) =
      δ (GeneralLinearGroup.det g) := by
    intro j
    change (η j * δ) (GeneralLinearGroup.det g) = _
    rw [MonoidHom.mul_apply, hη j _ hval, one_mul]
  have hΦ := hasTypes_apply_mul_left_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 1))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl) (hL.1 s 0 rfl) hg hint
  have hTop := hasTypes_apply_mul_right_of_mem_J_KO (μ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).mu (s + 2))
    (Φ := (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop) hL.2 hg hint
  rw [hmu] at hΦ hTop
  have hΦ' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl (g.val * B) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).Phi s 0 rfl B := by
    intro B
    rw [hΦ B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hTop' : ∀ B, (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop (B * g.val) =
      c * (_root_.GlobalTheory.StepData.twistChain s t κ δ hδ η).PhiTop B := by
    intro B
    rw [hTop B, hc, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  obtain ⟨G, hGi, hGeq⟩ : ∃ G : GL (_root_.GlobalTheory.StepData.XIx κ t (s + 1)) k,
      G ∈ _root_.GlobalTheory.SplitWeil.KO k _ ∧ (G : Matrix _ _ k) = g.val.toBlocks₁₁ :=
    ⟨_root_.GlobalTheory.StepData.reGL (Equiv.sumEmpty _ (Fin 0)) g, reGL_mem_KO_of_mem_KO _ hint, by
      rw [_root_.GlobalTheory.StepData.reGL_val]
      rfl⟩
  refine ⟨c, hroot, ?_, ?_⟩
  · intro h x₀ y
    unfold _root_.GlobalTheory.StepData.Chain.Psi
    rw [withCol_toBlocks11_mul_mulVec_eq_mul_withCol]
    simp only [_root_.GlobalTheory.SplitWeil.om, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [hΦ']
    ring
  · intro ψ ε w y x
    unfold _root_.GlobalTheory.StepData.Chain.xiTop
    rw [fromCols_zero_mul_toBlocks11_eq_mul_val, mul_apply_inr_unit_eq_vecMul]
    erw [hTop']
    rw [← hGeq, hat_cosetInd_box_vecMul_KO_eq_mulVec ν ψ ε G hGi w y]
    ring

end GlobalTheory.LevelLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnityStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  exact @GlobalTheory.LevelLaw.last_steps_law
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.TwPlaces

theorem rou_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

theorem rou_inv {x : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ x⁻¹ ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := hx
  exact ⟨n, hn, by rw [inv_pow, hx, inv_one]⟩

theorem rou_prod {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ f i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, f i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact rou_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem rou_circle {x : Circle} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ (x : ℂ) ^ n = 1 := by
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, hn, by rw [← Circle.coe_pow, hx, Circle.coe_one]⟩

theorem toLoc_frames {E k : Type} [Field E] [Field k] (ι : E →+* k) {A C : Type} [Fintype A] [Fintype C] {a b a' b' : ℕ}
    (ha : a' = a) (hb : b' = b) (e : C ≃ Fin b) (e' : A ≃ Fin a) (f' : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (f : (Fin b → E) ≃ₗ[E] (Fin b → E)) (z : Matrix (Fin b') (Fin a') E) (M : Matrix (Fin b') C k) (M' : Matrix (Fin a') A k)
    (hM : ∀ r c, ι (f (Pi.single (e c) 1) (finCongr hb r)) = M r c)
    (hM' : ∀ r c, ι (f' (Pi.single (e' c) 1) (finCongr ha r)) = M' r c) :
    M * (GlobalTheory.SymBridge.toLoc ι e e' (Formalism.L2.Col.inFr f' f (Matrix.toLin' (z.reindex (finCongr hb) (finCongr ha)))) : Matrix C A k) =
      z.map ι * M' := by
  subst ha hb
  have key : ∀ (y : Fin b' → E) r, ∑ c, M r c * ι (f.symm y (e c)) = ι (y r) := by
    intro y r
    have h4 : y = ∑ c, f.symm y (e c) • f (Pi.single (e c) 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun b _ => map_smul _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [h4, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hM r c, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]
    rfl
  ext r c
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (key (Matrix.toLin' (z.reindex (finCongr rfl) (finCongr rfl)) (f' (Pi.single (e' c) 1))) r).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, ← hM' q c]
  rfl

theorem frame_cancel {k : Type} [Field k] {N N' : ℕ} {Y Y' : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    {T : Matrix Y Y' k} {z : Matrix (Fin N) (Fin N') k} {M : Matrix (Fin N') Y' k} (h : F.β * T = z * M) : T = F.γ * z * M := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

theorem isLocFac_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (hd : DenseRange (ofSplit q).pr) (ψ : AddChar (AF D.host.F) ℂ) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : ∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) (eT : ∀ z, z ∈ LT ↔ z ∈ intVec D T.rank)
    (fS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (fT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (c : WO S T →₀ ℂ) (Ξk : Matrix Y Y' k → ℂ) (hSB : Ξk ∈ SB (Matrix Y Y' k)) (hc : (ofSplit q).IsCombAt ψ FS FT c Ξk)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (hΞ : ∀ z, Ξ z = Ξk (FT.γ * z.map (ofSplit q).pr * FS.β)) :
    GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξ ∧ GlobalTheory.FinPl.CombAt (· = q.v) c :=
  ⟨⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ofSplit q, Y, Y', inferInstance, inferInstance, inferInstance,
    inferInstance, FS, FT, Ξk, hd, hq,
    GlobalTheory.StdHomAt.int_iff_up_mem_stdHom D k q hU Y Y' S T FS FT LS LT hS hT eS eT fS fT, hSB, hc, hΞ⟩,
    fun u hu r s => (GlobalTheory.FinPl.FrameLat.idem_iff q _).2 (hc.1 u hu r s)⟩

theorem xiTop_mem_SB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (w : kˣ)
    (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) w) : T.xiTop (box _ w) ψ ν (-1) yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hv1 : valuation k (-1 : k) = 1 := by simp
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν (-1) hψ hν hv1 (X (s + 1)) 1 1 _ (cosetInd_mem_SB w yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

section Steps

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T} (J : QJ a t) (i : Fin J.r)

variable {J i}

theorem even_ranks (R : Ranks) (j : ℕ) (h : j + 2 < R.m) :
    Even (R.N j + Formalism.L2.Col.cOf R j + (R.N (j + 1 + 1) + Formalism.L2.Col.cOf R (j + 1 + 1))) := by
  obtain ⟨c, hc⟩ : ∃ c, R.m = j + 3 + c := ⟨R.m - (j + 3), by omega⟩
  have e1 : Formalism.L2.Col.cOf R j = c + 2 := by unfold Formalism.L2.Col.cOf; omega
  have e2 : Formalism.L2.Col.cOf R (j + 1 + 1) = c := by unfold Formalism.L2.Col.cOf; omega
  rw [e1, e2]
  show Even (R.k + j * (R.t + 1) + (c + 2) + (R.k + (j + 1 + 1) * (R.t + 1) + c))
  exact ⟨R.k + (j + 1) * (R.t + 1) + c + 1, by ring⟩

end Steps

end GlobalTheory.TwPlaces

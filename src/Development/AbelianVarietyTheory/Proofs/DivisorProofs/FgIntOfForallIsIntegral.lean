module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
open NumberField

namespace GlobalTheory

theorem fg_int_of_forall_isIntegral (K' : Type) [Field K'] [NumberField K']
    (M : Submodule ℤ K') (hM : ∀ y ∈ M, IsIntegral ℤ y) : M.FG := by
  let f : 𝓞 K' →ₗ[ℤ] K' := (algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap
  have hle : M ≤ LinearMap.range f := fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩
  have hfg : (M.comap f).FG := IsNoetherian.noetherian _
  have hmap := hfg.map f
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at hmap

theorem fg_of_integral_functionals (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  suffices H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by
    simpa using H ⊤
  intro W
  induction W using WellFoundedLT.induction with
  | _ W ih =>
    by_cases hW : W = ⊥
    · subst hW
      have hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥ := by
        ext y
        simp
      rw [hbot]
      exact Submodule.fg_bot
    · obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨K', _, _, _, φ, hφx, hφL⟩ := h x hx0
      let f : C →ₗ[ℤ] K' := φ.toAddMonoidHom.toIntLinearMap
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => hφx ?_
        have hx : x ∈ W ⊓ LinearMap.ker φ := by rw [heq]; exact hxW
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
      apply Submodule.fg_of_fg_map_of_fg_inf_ker f
      · apply fg_int_of_forall_isIntegral K'
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact hφL y (Submodule.mem_inf.mp hy).1
      · have heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f
            = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ := by
          ext y
          simp [f, and_assoc]
          exact fun _ _ => Iff.rfl
        rw [heq]
        exact ih _ hlt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
noncomputable section

namespace GlobalTheory.ValIwasawa

open Matrix

variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


variable (V) in
abbrev valI : Valuation F (ValuationRing.ValueGroup V F) := ValuationRing.valuation V F

theorem exists_of_valI_le_one {x : F} (h : valI (V := V) x ≤ 1) : ∃ a : V, algebraMap V F a = x :=
  (ValuationRing.mem_integer_iff V F x).1 h

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun r => valI (V := V) (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI (V := V)).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.toPEquiv.toMatrix
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI (V := V) (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_lowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa_matrix : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U := by
  intro n
  induction n with
  | zero =>
    intro A _
    exact ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) (n := n) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := ih (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem iwasawa : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (N : ℕ) (g : GL (Fin N) K), ∃ (k : GL (Fin N) V) (b : GL (Fin N) K),
    b.1.BlockTriangular id ∧ g = GeneralLinearGroup.map (algebraMap V K) k * b := by
  intro V K _ _ _ _ _ _ N g
  obtain ⟨k, U, hk, hU, -, hg⟩ := iwasawa_matrix (V := V) g.1 (Matrix.GeneralLinearGroup.det_ne_zero g)
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk
  refine ⟨u, (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g, ?_, by simp⟩
  have : ((GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g).1 = U := by
    have h1 : g.1 = (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u).1 * U := hg
    rw [Units.val_mul, h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [this]
  exact hU

end GlobalTheory.ValIwasawa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
open Matrix

namespace GlobalTheory

theorem exists_rows_linearIndependent_of_le_rank {K m n : Type} [Field K] [Fintype m] [Fintype n]
    (ρ : ℕ) (M : Matrix m n K) (h : ρ ≤ M.rank) :
    ∃ S : Fin ρ → m, LinearIndependent K (M.submatrix S id).row := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = M.rank := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row]
  have hle : Fintype.card (Fin ρ) ≤ Fintype.card κ := by rw [hκ, Fintype.card_fin]; exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  exact ⟨a ∘ f, hli.comp f f.injective⟩

theorem exists_submatrix_det_ne_zero_of_le_rank :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by
  intro k _ A D _ _ _ _ ρ Y h
  obtain ⟨S, hS⟩ := exists_rows_linearIndependent_of_le_rank ρ Y h
  have hZ : (Y.submatrix S id).rank = ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hS, Fintype.card_fin]
  have hZt : ρ ≤ (Y.submatrix S id)ᵀ.rank := by rw [Matrix.rank_transpose, hZ]
  obtain ⟨τ, hτ⟩ := exists_rows_linearIndependent_of_le_rank ρ (Y.submatrix S id)ᵀ hZt
  refine ⟨S, τ, ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
  have e : (Y.submatrix S id)ᵀ.submatrix τ id = (Y.submatrix S τ)ᵀ := by ext i j; rfl
  rw [e, Matrix.det_transpose] at hu
  exact hu.ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRankStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_minor_of_rank : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
noncomputable section

open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform

namespace GlobalTheory.RealWeil

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def gau (u : V) : ℂ := cexp (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2)

def IsHeis (om : V → V → ℝ) (ρ : V → B →L[ℂ] B) : Prop :=
  (∀ f, ρ 0 f = f) ∧ (∀ u v f, ρ u (ρ v f) = cexp (π * I * (om u v : ℂ)) • ρ (u + v) f) ∧
    (∀ u f, ‖ρ u f‖ = ‖f‖) ∧ ∀ f, Continuous fun u => ρ u f

def Sm (ρ : V → B →L[ℂ] B) (f : B) : Prop := ContDiff ℝ ∞ fun v => ρ v f

def IsOsc (ρ : V → B →L[ℂ] B) {G : Type} [Group G] (k : G → V → V) (Ω : G → B → B) : Prop :=
  (∀ g f f', Sm ρ f → Sm ρ f' → Ω g (f + f') = Ω g f + Ω g f') ∧
  (∀ g (a : ℂ) f, Sm ρ f → Ω g (a • f) = a • Ω g f) ∧
  (∀ g f, Sm ρ f → Sm ρ (Ω g f)) ∧
  (∀ f, Sm ρ f → Ω 1 f = f) ∧
  (∀ g g' f, Sm ρ f → Ω (g * g') f = Ω g (Ω g' f)) ∧
  (∀ g v f, Sm ρ f → Ω g (ρ v f) = ρ (k g v) (Ω g f)) ∧
  (∀ g (A : B →L[ℂ] B), (∀ v f, A (ρ v f) = ρ v (A f)) → ∀ f, Sm ρ f → Ω g (A f) = A (Ω g f)) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H),
    (∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) → ∀ g f, Sm ρ f → ‖Φ (Ω g f)‖ = ‖Φ f‖

theorem norm_gau (u : V) : ‖gau u‖ = Real.exp (-(π / 2) * ‖u‖ ^ 2) := by
  unfold gau
  rw [Complex.norm_exp]
  congr 1
  have : (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-(π / 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]

theorem gau_ne_zero (u : V) : gau u ≠ 0 := Complex.exp_ne_zero _

theorem gau_zero : gau (0 : V) = 1 := by simp [gau]

theorem gau_neg (u : V) : gau (-u) = gau u := by simp [gau]

theorem continuous_gau : Continuous (gau : V → ℂ) := by unfold gau; fun_prop

theorem IsHeis.twist {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) (g : V →L[ℝ] V)
    (hg : ∀ x y, om (g x) (g y) = om x y) : IsHeis om fun v => ρ (g v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hg, map_add (f := _)], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp g.continuous⟩

theorem IsHeis.continuous {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) {Y : Type} [TopologicalSpace Y]
    {a : Y → V} {x : Y → B} (ha : Continuous a) (hx : Continuous x) : Continuous fun y => ρ (a y) (x y) := by
  have : Continuous fun p : B × V => ρ p.2 p.1 :=
    continuous_prod_of_continuous_lipschitzWith (fun p : B × V => ρ p.2 p.1) 1
      (fun f => h.2.2.2 f) fun v => LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub, h.2.2.1]; simp
  exact this.comp (hx.prodMk ha)

end General

def dP {ι : Type} [Fintype ι] [DecidableEq ι] (s g : Matrix ι ι ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)).det

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def omJ (J : V ≃ₗᵢ[ℝ] V) (x y : V) : ℝ := ⟪x, J y⟫

def lam (g : V → V) : ℂ := ∫ u, gau u * gau (g u)

def mu (J : V ≃ₗᵢ[ℝ] V) (g₁ g₂ : V → V) : ℂ :=
  ∫ u, ∫ v, gau u * gau v * (cexp (π * I * (omJ J (g₁ u) (g₂ v) : ℂ)) * gau (g₁ u + g₂ v))

theorem integrable_gau : Integrable (gau : V → ℂ) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (π / 2 : ℂ)) (by simpa using Real.pi_pos) 0 0
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [gau]

variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

omit [CompleteSpace B] in
theorem IsHeis.integrable (h : IsHeis om ρ) (f : B) : Integrable fun u => gau u • ρ u f := by
  refine Integrable.mono' ((integrable_gau (V := V)).norm.mul_const ‖f‖)
    (continuous_gau.smul (h.2.2.2 f)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_smul, h.2.2.1]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B] in
theorem IsHeis.continuous_gau_smul (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f :=
  continuous_gau.smul (h.2.2.2 f)

def proj (h : IsHeis om ρ) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u, gau u • ρ u f
      map_add' := fun f f' => by
        rw [← integral_add (h.integrable f) (h.integrable f')]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm a] }
    (∫ u : V, ‖gau u‖) fun f => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [norm_smul, h.2.2.1]
      rw [integral_mul_const]

omit [CompleteSpace B] in
theorem proj_apply (h : IsHeis om ρ) (f : B) : proj h f = ∫ u, gau u • ρ u f := rfl

def Good (h : IsHeis om ρ) (f : B) : Prop := ∀ n : ℕ, Integrable fun w => ‖w‖ ^ n * ‖proj h (ρ (-w) f)‖

variable {J : V ≃ₗᵢ[ℝ] V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem omJ_skew (hJ : ∀ x, J (J x) = -x) (x y : V) : omJ J y x = -omJ J x y := by
  unfold omJ
  rw [← J.inner_map_map, hJ, inner_neg_right, real_inner_comm]

theorem proj_translate (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (w : V) :
    proj h (ρ (-w) f) = ρ (-w) (𝓕 (fun u => gau u • ρ u f) (J w)) := by
  rw [proj_apply, Real.fourier_eq', ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_smul, h.2.1, smul_smul]
    rw [add_comm (-w) u, omJ_skew hJ u (-w)]
    congr 1
    have e : omJ J u (-w) = -⟪u, J w⟫ := by simp [omJ]
    rw [e, mul_right_comm _ (gau u), ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  · have := (Real.fourierIntegral_convergent_iff (J w)).2 (h.integrable f)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul, Complex.ofReal_neg] using this

theorem Good.fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) (n : ℕ) :
    Integrable fun w => ‖w‖ ^ n * ‖𝓕 (fun u => gau u • ρ u f) w‖ := by
  have := hf n
  simp only [proj_translate hJ, h.2.2.1] at this
  rw [← J.measurePreserving.integrable_comp_emb J.toHomeomorph.measurableEmbedding]
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp

theorem continuous_fourier_gau (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (h.integrable f)

theorem Good.integrable_fourier (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable (𝓕 fun u => gau u • ρ u f) := by
  have := hf.fourier hJ 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff (continuous_fourier_gau h f).aestronglyMeasurable).1 this

theorem Good.inversion (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    ∫ w, ρ w (proj h (ρ (-w) f)) = f := by
  have e : ∀ w, ρ w (proj h (ρ (-w) f)) = 𝓕 (fun u => gau u • ρ u f) (J w) := by
    intro w
    have h0 : omJ J w (-w) = 0 := by
      have := omJ_skew hJ w w
      have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
      linarith
    rw [proj_translate hJ, h.2.1, h0, add_neg_cancel, h.1]
    simp
  simp only [e]
  rw [J.measurePreserving.integral_comp J.toHomeomorph.measurableEmbedding]
  have := congrFun ((h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f)
    (hf.integrable_fourier hJ)) 0
  rw [Real.fourierInv_eq] at this
  simpa [gau_zero, h.1] using this

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_gau_inv : ContDiff ℝ ∞ fun u : V => (gau u)⁻¹ := by
  have : (fun u : V => (gau u)⁻¹) = fun u => cexp ((π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    rw [gau, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [this]
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)))

theorem Good.sm (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) : Sm ρ f := by
  have h1 := (h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f) (hf.integrable_fourier hJ)
  have h2 : ContDiff ℝ ∞ (𝓕 (𝓕 fun u => gau u • ρ u f)) := Real.contDiff_fourier fun n _ => hf.fourier hJ n
  have h3 : ContDiff ℝ ∞ fun u => gau u • ρ u f := by
    rw [← h1]
    have : 𝓕⁻ (𝓕 fun u => gau u • ρ u f) = fun u => 𝓕 (𝓕 fun u => gau u • ρ u f) (-u) := by
      funext u; rw [Real.fourierInv_eq_fourier_neg]
    rw [this]
    exact h2.comp contDiff_neg
  have : ContDiff ℝ ∞ fun u => (gau u)⁻¹ • gau u • ρ u f := (contDiff_gau_inv (V := V)).smul h3
  simpa only [smul_smul, inv_mul_cancel₀ (gau_ne_zero _), one_smul, Sm] using this

end Inner

end GlobalTheory.RealWeil

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LawDer

variable {R : Type} [CommRing R] {d : ℕ}

def atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ => 0) H

def invDer (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u : Fin d → R)
    (F : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ i, u i • atZero (pderiv (R := R) (Sum.inr i) (subst μ F))

end GlobalTheory.LawDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
open Real

namespace GlobalTheory

theorem zetaTerm_tsum_le_two (i : ℕ) (hi : 2 ≤ i) :
    ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ 2 := by
  have h2 : HasSum (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) (π^2/6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hle : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+1)^i ≤ 1/((n:ℝ)+1)^2 := by
    intro n
    have h1 : (1:ℝ) ≤ (n:ℝ)+1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ h1 hi
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ 1/((n:ℝ)+1)^i := fun n => by positivity
  have hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^i) :=
    Summable.of_nonneg_of_le hnn hle h2.summable
  calc ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ ∑' n : ℕ, 1/((n:ℝ)+1)^2 := hs.tsum_le_tsum hle h2.summable
    _ = π^2/6 := h2.tsum_eq
    _ ≤ 2 := by
      have := Real.pi_lt_d2
      have := Real.pi_pos
      nlinarith

theorem volumeConstant_le (r : ℕ) (hr : 2 ≤ r) :
    √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by
  have hprod : ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ ∏ _i ∈ Finset.Icc 2 r, (2:ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact tsum_nonneg (fun n => by positivity)
    · intro i hi; exact zetaTerm_tsum_le_two i (Finset.mem_Icc.mp hi).1
  rw [Finset.prod_const, Nat.card_Icc] at hprod
  have hexp : r + 1 - 2 ≤ r*(r-1)/2 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : k + 2 + 1 - 2 = k + 1 := by omega
    have h' : k + 2 - 1 = k + 1 := by omega
    rw [this, h']
    nlinarith
  have hpow : (2:ℝ)^(r+1-2) ≤ 2^(r*(r-1)/2) := pow_le_pow_right₀ (by norm_num) hexp
  have hpi : (1:ℝ) ≤ (2*π)^(r-1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : 0 ≤ √(r:ℝ) := Real.sqrt_nonneg _
  have h2p : (0:ℝ) ≤ 2^(r*(r-1)/2) := by positivity
  calc √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i)
      ≤ √r * 2^(r*(r-1)/2) := mul_le_mul_of_nonneg_left (hprod.trans hpow) hsq
    _ ≤ √r * (2^(r*(r-1)/2) * (2*π)^(r-1)) := by
        apply mul_le_mul_of_nonneg_left _ hsq
        nlinarith
    _ = 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
open Matrix
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem posDef_exists_invertible_conjTranspose_mul_self {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosDef) :
    ∃ R Ri : Matrix (Fin n) (Fin n) ℂ, R * Ri = 1 ∧ Ri * R = 1 ∧ P = Rᴴ * R := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hP.posSemidef.nonneg
  have hd : IsUnit R.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have h1 := hP.det_pos
    rw [hR, Matrix.det_mul, h] at h1
    simp at h1
  exact ⟨R, R⁻¹, Matrix.mul_nonsing_inv R hd, Matrix.nonsing_inv_mul R hd, hR⟩

theorem hermitian_involution_unitary_blocks {n : ℕ} (t : Matrix (Fin n) (Fin n) ℂ)
    (hH : tᴴ = t) (ht : t * t = 1) :
    ∃ (p q : ℕ) (V : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧
      Vᴴ * t * V = Matrix.fromBlocks 1 0 0 (-1) := by
  classical
  have hH' : t.IsHermitian := hH
  set U : Matrix (Fin n) (Fin n) ℂ := (hH'.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := fun i => ((hH'.eigenvalues i : ℝ) : ℂ) with hd
  have hspec : t = U * diagonal d * Uᴴ := by
    have := hH'.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  have hUU : U * Uᴴ = 1 := by
    have := hH'.eigenvectorUnitary.2.2
    simpa [star_eq_conjTranspose] using this
  have hUU' : Uᴴ * U = 1 := by
    have := hH'.eigenvectorUnitary.2.1
    simpa [star_eq_conjTranspose] using this
  have hD : Uᴴ * t * U = diagonal d := by
    rw [hspec]
    calc Uᴴ * (U * diagonal d * Uᴴ) * U = (Uᴴ * U) * diagonal d * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hUU']; simp
  have hDD : diagonal d * diagonal d = 1 := by
    rw [← hD]
    calc Uᴴ * t * U * (Uᴴ * t * U) = Uᴴ * (t * (U * Uᴴ) * t) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, ht, Matrix.mul_one, hUU']
  have hsq : ∀ i, d i * d i = 1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    simpa [diagonal_mul_diagonal] using this
  let e : Fin (Fintype.card {i // d i = 1}) ⊕ Fin (Fintype.card {i // ¬ d i = 1}) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
      (Equiv.sumCompl (fun i => d i = 1))
  have he1 : ∀ a, d (e (Sum.inl a)) = 1 := fun a => ((Fintype.equivFin {i // d i = 1}).symm a).2
  have he2 : ∀ a, d (e (Sum.inr a)) = -1 := fun a =>
    (mul_self_eq_one_iff.1 (hsq _)).resolve_left
      ((Fintype.equivFin {i // ¬ d i = 1}).symm a).2
  refine ⟨_, _, U.submatrix id e, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, hUU, submatrix_id_id]
  · rw [conjTranspose_submatrix]
    have := Matrix.submatrix_mul_equiv Uᴴ U e (Equiv.refl _) e
    simp only [Equiv.coe_refl] at this
    rw [this, hUU', submatrix_one_equiv]
  · have h1 : (U.submatrix id e)ᴴ * t * U.submatrix id e = (Uᴴ * t * U).submatrix e e := by
      ext a b
      simp [Matrix.mul_apply]
    rw [h1, hD, submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [diagonal_apply, he1, he2, Matrix.one_apply]
    split_ifs <;> simp

theorem exists_basis_adapted_to_cartan_involution :
    ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef →
      ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
        (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧
        Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧
        s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by
  intro n G s hs hG hP
  obtain ⟨R, Ri, h1, h2, hR⟩ := posDef_exists_invertible_conjTranspose_mul_self _ hP
  have hG1 : G = Rᴴ * R * s := by rw [← hR, Matrix.mul_assoc, hs, Matrix.mul_one]
  have hG2 : G = sᴴ * (Rᴴ * R) := by rw [← hR, ← Matrix.mul_assoc, hG]
  have h3 : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hGt : Riᴴ * G * Ri = R * s * Ri := by
    rw [hG1]
    calc Riᴴ * (Rᴴ * R * s) * Ri = (Riᴴ * Rᴴ) * (R * s * Ri) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  have hherm : (R * s * Ri)ᴴ = R * s * Ri := by
    rw [← hGt]
    conv_rhs => rw [hG2]
    rw [hGt]
    calc (R * s * Ri)ᴴ = Riᴴ * sᴴ * Rᴴ * (R * Ri) := by
          rw [h1]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hinv : (R * s * Ri) * (R * s * Ri) = 1 := by
    calc (R * s * Ri) * (R * s * Ri) = R * (s * (Ri * R) * s) * Ri := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hs, Matrix.mul_one, h1]
  obtain ⟨p, q, V, hV1, hV2, hV3⟩ := hermitian_involution_unitary_blocks _ hherm hinv
  refine ⟨p, q, Ri * V, Vᴴ * R, ?_, ?_, ?_, ?_⟩
  · calc Ri * V * (Vᴴ * R) = Ri * (V * Vᴴ) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, h2]
  · calc Vᴴ * R * (Ri * V) = Vᴴ * (R * Ri) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV2]
  · rw [← hV3, ← hGt]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  · rw [← hV3]
    symm
    calc Ri * V * (Vᴴ * (R * s * Ri) * V) = Ri * (V * Vᴴ) * R * (s * (Ri * V)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV1, Matrix.mul_one, h2, Matrix.one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
namespace GlobalTheory.Div.BlockChangeDet

open Matrix

theorem det_blockDiagonal'_eq_prod {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm

theorem det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  classical

  have hli : LinearIndependent F ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : (0 : N) = ∑ k, (0 : (Σ b, Fin (m b)) → F) k • ℓ k := by simp
    have := (hℓ 0).unique ha.symm h0
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span F (Set.range ℓ) := by
    intro x _
    obtain ⟨a, ha, -⟩ := hℓ x
    rw [ha]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfr : Module.finrank F N = n := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_congr e, Fintype.card_fin]
  have hspnu : ⊤ ≤ Submodule.span F (Set.range nu) := by
    refine le_trans hsp (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, rfl⟩
    rw [hU σ]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hlinu : LinearIndependent F nu :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspnu (by simp [hfr])
  have uniq : ∀ a c : Fin n → F, ∑ k, a k • nu k = ∑ k, c k • nu k → a = c := by
    intro a c h
    have := Fintype.linearIndependent_iff.mp hlinu (a - c)
      (by simp [sub_smul, Finset.sum_sub_distrib, h])
    funext k
    exact sub_eq_zero.mp (this k)

  have hdet : U.det ≠ 0 := by
    have hrows : LinearIndependent F (fun i => U i) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hli' : LinearIndependent F (ℓ ∘ e.symm) := hli.comp e.symm e.symm.injective
      refine Fintype.linearIndependent_iff.mp hli' a ?_
      have hcol : ∀ k, ∑ i, a i * U i k = 0 := by
        intro k
        have := congrFun ha k
        simpa [Finset.sum_apply] using this
      calc ∑ i, a i • (ℓ ∘ e.symm) i
          = ∑ i, a i • ∑ k, U i k • nu k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Function.comp, hU]
        _ = ∑ k, (∑ i, a i * U i k) • nu k := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [hcol]
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact (Matrix.isUnit_iff_isUnit_det U |>.mp hu).ne_zero
  refine ⟨hdet, ?_⟩

  have hent : ∀ σ k, ∑ τ, blockDiagonal' g σ τ * U (e τ) k = ∑ l, C σ l * A l k := by
    rintro ⟨b, i⟩
    have h1 : ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ = ∑ j, g b i j • ℓ ⟨b, j⟩ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [blockDiagonal'_apply_eq]
      · intro b' _ hb'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [blockDiagonal'_apply_ne g i j (Ne.symm hb'), zero_smul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have h2 : ∑ k, (∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k) • nu k
        = ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ := by
      simp only [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : ∑ k, (∑ l, C ⟨b, i⟩ l * A l k) • nu k = ∑ l, C ⟨b, i⟩ l • mu l := by
      simp only [hA, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have := uniq (fun k => ∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k)
      (fun k => ∑ l, C ⟨b, i⟩ l * A l k) (by rw [h2, h1, hg b i, ← h3])
    intro k
    exact congrFun this k
  have key : Matrix.reindex e e (blockDiagonal' g) * U
      = (Matrix.of fun i k => C (e.symm i) k) * A := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [← hent (e.symm i) k]
    exact Fintype.sum_equiv e.symm _ _ (fun x => by simp)
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, det_blockDiagonal'_eq_prod] at this
  exact this

theorem det_block_change' : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  intro F _ N _ _ κ _ m n e ℓ hℓ nu mu U A C g hU hA hg
  exact det_block_change F m e ℓ hℓ nu mu U A C g hU hA hg

end GlobalTheory.Div.BlockChangeDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicitStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  first | exact @GlobalTheory.Div.BlockChangeDet.det_block_change' | exact GlobalTheory.Div.BlockChangeDet.det_block_change' | (intros; apply GlobalTheory.Div.BlockChangeDet.det_block_change' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

variable {E : Type} [Field E] [NumberField E]

def scLat {n : ℕ} (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ}
  zero_mem' := fun c _ => by rw [smul_zero]; exact Λ.zero_mem
  add_mem' := fun hx hy c hc => by rw [smul_add]; exact Λ.add_mem (hx c hc) (hy c hc)
  smul_mem' := fun r y hy c hc => by rw [smul_comm]; exact Λ.smul_mem r (hy c hc)

theorem mem_scLat {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := Iff.rfl

def blkA {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin a → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inl)

def blkB {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin b → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inr)

def pairLat {a b d : ℕ} (ΛA : Submodule (𝓞 E) (Fin a → E)) (ΛB : Submodule (𝓞 E) (Fin b → E))
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule (𝓞 E) (Fin d → E) :=
  ΛA.comap (blkA e) ⊓ ΛB.comap (blkB e)

theorem mem_pairLat {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := Iff.rfl

end GlobalTheory.SkewLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
namespace GlobalTheory.EtC

def IsExcisionNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  Algebra.Etale A A' ∧ (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
    ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}

theorem isExcisionNbhd_self (A : Type) [CommRing A] (f : A) : IsExcisionNbhd A A f :=
  ⟨inferInstance, fun a' => ⟨a', by simp⟩, fun a h => by simpa using h⟩

end GlobalTheory.EtC
end

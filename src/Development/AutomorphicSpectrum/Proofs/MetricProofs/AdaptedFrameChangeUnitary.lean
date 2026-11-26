module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply, ← fromBlocks_one]

theorem unitary_of_blocks {j j' : ℕ} (u : Matrix (Sg j j') (Sg j j') ℂ) (hu : uᴴ * sgI j j' * u = sgI j j')
    (h21 : u.toBlocks₂₁ = 0) (h12 : u.toBlocks₁₂ = 0) : uᴴ * u = 1 := by
  have hb : u = fromBlocks u.toBlocks₁₁ 0 0 u.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks u, h21, h12]
  generalize u.toBlocks₁₁ = a at hb
  generalize u.toBlocks₂₂ = d at hb
  subst hb
  have h := hu
  simp only [sgI, fromBlocks_conjTranspose, fromBlocks_multiply] at h
  obtain ⟨h1, -, -, h2⟩ := fromBlocks_inj.1 h
  have h1' : aᴴ * a = 1 := by
    simpa using h1
  have h2' : dᴴ * d = 1 := by
    simpa using h2
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, h1', h2', ← fromBlocks_one]

theorem blocks_of_unitary {j j' : ℕ} (u : Matrix (Sg j j') (Sg j j') ℂ) (hu : uᴴ * sgI j j' * u = sgI j j')
    (h : uᴴ * u = 1) : u.toBlocks₂₁ = 0 ∧ u.toBlocks₁₂ = 0 := by
  have h' : u * uᴴ = 1 := mul_eq_one_comm.1 h
  have hcomm : sgI j j' * u = u * sgI j j' := by
    calc sgI j j' * u = (u * uᴴ) * sgI j j' * u := by rw [h', one_mul]
      _ = u * (uᴴ * sgI j j' * u) := by simp only [Matrix.mul_assoc]
      _ = u * sgI j j' := by rw [hu]
  rw [← fromBlocks_toBlocks u] at hcomm
  simp only [sgI, fromBlocks_multiply] at hcomm
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul] at hcomm
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.1 hcomm
  constructor
  · ext a b
    have := congrFun (congrFun h21 a) b
    simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
    exact neg_eq_self.1 this
  · ext a b
    have := congrFun (congrFun h12 a) b
    simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
    exact self_eq_neg.1 this

def imLin {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r a := by
    have : star (r • a) = (r : ℂ) • star a := by
      ext i; simp
    simp [this, mulVec_smul, dotProduct_smul]

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

theorem perExt_injective : Function.Injective (C.perExt R) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hcoord : ∀ l, C.bas.equivFun y l = 0 := by
    intro l
    obtain ⟨x, hx⟩ := R.unimod.2 (C.lam.coord l)
    have key : imLin R.Hm (R.P x) (C.perExt R y) = C.bas.equivFun y l := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LatEmb.perExt, Module.Basis.constr_apply_fintype, map_sum]
      have hk : ∀ k, imLin R.Hm (R.P x) (R.P (C.lam k)) = if k = l then 1 else 0 := by
        intro k
        have h1 : imLin R.Hm (R.P x) (R.P (C.lam k)) = (R.form x (C.lam k) : ℝ) := R.im x _
        rw [h1, hx]
        simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
      simp [hk]
    rw [← key, hy, map_zero]
  have : C.bas.equivFun y = 0 := funext hcoord
  simpa using this

open Classical in
theorem pPart_add (τ : Ψ) (y y' : Fin (j + j') → ℂ) :
    C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add (f := _)]
  module

open Classical in
theorem pBar_add (τ : Ψ) (y y' : Fin (j + j') → ℂ) :
    C.pBar R τ (y + y') = C.pBar R τ y + C.pBar R τ y' := by
  simp only [LatEmb.pBar, smul_add, Pi.single_add, map_add (f := _)]
  module

open Classical in
theorem pPart_add_pBar (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.pPart R τ y + C.pBar R τ y = C.perExt R (Pi.single τ y) := by
  simp only [LatEmb.pPart, LatEmb.pBar]
  module

theorem eq_zero_of_parts (τ : Ψ) (y : Fin (j + j') → ℂ) (h : C.pPart R τ y = 0) (h' : C.pBar R τ y = 0) : y = 0 := by
  classical
  have h0 : C.perExt R (Pi.single τ y) = 0 := by
    rw [← pPart_add_pBar, h, h', add_zero]
  have h1 : (Pi.single τ y : Ψ → Fin (j + j') → ℂ) = 0 := (injective_iff_map_eq_zero _).1 (perExt_injective C R) _ h0
  simpa using congrFun h1 τ

variable {C}

theorem cinv_mul {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    C.cinv A τ * A = 1 := by
  calc C.cinv A τ * A = sgI j j' * (Aᴴ * C.sgr τ * A) := by
        simp only [LatEmb.cinv, Matrix.mul_assoc]
    _ = 1 := by rw [h, sgI_mul_self]

theorem mul_cinv {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    A * C.cinv A τ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (cinv_mul h)

theorem sgr_eq {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j') :
    C.sgr τ = (C.cinv A τ)ᴴ * sgI j j' * C.cinv A τ := by
  have h1 : (C.cinv A τ)ᴴ * Aᴴ = 1 := by
    rw [← conjTranspose_mul, mul_cinv h, conjTranspose_one]
  calc C.sgr τ = ((C.cinv A τ)ᴴ * Aᴴ) * C.sgr τ * (A * C.cinv A τ) := by rw [h1, mul_cinv h, one_mul, mul_one]
    _ = (C.cinv A τ)ᴴ * (Aᴴ * C.sgr τ * A) * C.cinv A τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

theorem change_isSgU {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j')
    (h' : A'ᴴ * C.sgr τ * A' = sgI j j') :
    (C.cinv A τ * A')ᴴ * sgI j j' * (C.cinv A τ * A') = sgI j j' := by
  calc (C.cinv A τ * A')ᴴ * sgI j j' * (C.cinv A τ * A')
      = A'ᴴ * ((C.cinv A τ)ᴴ * sgI j j' * C.cinv A τ) * A' := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = sgI j j' := by rw [← sgr_eq h, h']

theorem mulVec_eq_zero {A : Matrix (Fin (j + j')) (Sg j j') ℂ} {τ : Ψ} (h : Aᴴ * C.sgr τ * A = sgI j j')
    {w : Sg j j' → ℂ} (hw : A *ᵥ w = 0) : w = 0 := by
  have : (C.cinv A τ * A) *ᵥ w = 0 := by
    rw [← mulVec_mulVec, hw, mulVec_zero]
  simpa [cinv_mul h] using this

theorem split_vec (w : Sg j j' → ℂ) : w = Sum.elim (w ∘ Sum.inl) (0 : Fin j' → ℂ) + Sum.elim (0 : Fin j → ℂ) (w ∘ Sum.inr) := by
  ext (i | i) <;> simp

theorem inr_eq_zero {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (w : Sg j j' → ℂ) (hw : C.pPart R τ (A τ *ᵥ w) = 0) (i : Fin j') : w (Sum.inr i) = 0 := by
  have h1 : C.pPart R τ (A τ *ᵥ Sum.elim (0 : Fin j → ℂ) (w ∘ Sum.inr)) = 0 := by
    rw [split_vec w, mulVec_add, pPart_add, hA.ker, zero_add] at hw
    simpa using hw
  have h2 := eq_zero_of_parts C R τ _ h1 (hA.kerBar τ _)
  have h3 := mulVec_eq_zero (hA.unit τ) h2
  simpa using congrFun h3 (Sum.inr i)

theorem inl_eq_zero {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (w : Sg j j' → ℂ) (hw : C.pBar R τ (A τ *ᵥ w) = 0) (i : Fin j) : w (Sum.inl i) = 0 := by
  have h1 : C.pBar R τ (A τ *ᵥ Sum.elim (w ∘ Sum.inl) (0 : Fin j' → ℂ)) = 0 := by
    rw [split_vec w, mulVec_add, pBar_add, hA.kerBar, add_zero] at hw
    simpa using hw
  have h2 := eq_zero_of_parts C R τ _ (hA.ker τ _) h1
  have h3 := mulVec_eq_zero (hA.unit τ) h2
  simpa using congrFun h3 (Sum.inl i)

theorem mulVec_inl (u : Matrix (Sg j j') (Sg j j') ℂ) (k : Fin j) (x : Sg j j') :
    (u *ᵥ Sum.elim (Pi.single k 1) (0 : Fin j' → ℂ)) x = u x (Sum.inl k) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply]

theorem mulVec_inr (u : Matrix (Sg j j') (Sg j j') ℂ) (k : Fin j') (x : Sg j j') :
    (u *ᵥ Sum.elim (0 : Fin j → ℂ) (Pi.single k 1)) x = u x (Sum.inr k) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply]

theorem mulVec_diag_inl (u : Matrix (Sg j j') (Sg j j') ℂ) (h : u.toBlocks₂₁ = 0) (v : Fin j → ℂ) :
    u *ᵥ Sum.elim v (0 : Fin j' → ℂ) = Sum.elim (u.toBlocks₁₁ *ᵥ v) (0 : Fin j' → ℂ) := by
  ext (i | i)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁]
  · have : ∀ k, u (Sum.inr i) (Sum.inl k) = 0 := fun k => congrFun (congrFun h i) k
    simp [mulVec, dotProduct, Fintype.sum_sum_type, this]

theorem mulVec_diag_inr (u : Matrix (Sg j j') (Sg j j') ℂ) (h : u.toBlocks₁₂ = 0) (v : Fin j' → ℂ) :
    u *ᵥ Sum.elim (0 : Fin j → ℂ) v = Sum.elim (0 : Fin j → ℂ) (u.toBlocks₂₂ *ᵥ v) := by
  ext (i | i)
  · have : ∀ k, u (Sum.inl i) (Sum.inr k) = 0 := fun k => congrFun (congrFun h i) k
    simp [mulVec, dotProduct, Fintype.sum_sum_type, this]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₂₂]

end Arch

theorem isAdapted_iff_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A' : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → (∀ τ, (A' τ)ᴴ * C.sgr τ * A' τ = sgI j j') → (C.IsAdapted R A' ↔ ∀ τ, (C.cinv (A τ) τ * A' τ)ᴴ * (C.cinv (A τ) τ * A' τ) = 1) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A A' _ hA hA'
  have hmul : ∀ τ, A τ * (C.cinv (A τ) τ * A' τ) = A' τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_cinv (hA.unit τ), Matrix.one_mul]
  constructor
  · intro hAd τ
    have h21 : (C.cinv (A τ) τ * A' τ).toBlocks₂₁ = 0 := by
      ext i k
      have hw : C.pPart R τ (A τ *ᵥ ((C.cinv (A τ) τ * A' τ) *ᵥ Sum.elim (Pi.single k 1) (0 : Fin j' → ℂ))) = 0 := by
        rw [mulVec_mulVec, hmul]
        exact hAd.ker τ _
      have := inr_eq_zero R hA τ _ hw i
      rwa [mulVec_inl] at this
    have h12 : (C.cinv (A τ) τ * A' τ).toBlocks₁₂ = 0 := by
      ext i k
      have hw : C.pBar R τ (A τ *ᵥ ((C.cinv (A τ) τ * A' τ) *ᵥ Sum.elim (0 : Fin j → ℂ) (Pi.single k 1))) = 0 := by
        rw [mulVec_mulVec, hmul]
        exact hAd.kerBar τ _
      have := inl_eq_zero R hA τ _ hw i
      rwa [mulVec_inr] at this
    exact unitary_of_blocks _ (change_isSgU (hA.unit τ) (hA' τ)) h21 h12
  · intro hu
    have hb := fun τ => blocks_of_unitary _ (change_isSgU (hA.unit τ) (hA' τ)) (hu τ)
    refine ⟨hA', fun τ v => ?_, fun τ v => ?_⟩
    · rw [← hmul τ, ← mulVec_mulVec, mulVec_diag_inl _ (hb τ).1]
      exact hA.ker τ _
    · rw [← hmul τ, ← mulVec_mulVec, mulVec_diag_inr _ (hb τ).2]
      exact hA.kerBar τ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitaryStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_change_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A' : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → (∀ τ, (A' τ)ᴴ * C.sgr τ * A' τ = sgI j j') → (C.IsAdapted R A' ↔ ∀ τ, (C.cinv (A τ) τ * A' τ)ᴴ * (C.cinv (A τ) τ * A' τ) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem star_dotProduct_mulVec_eq {I : Type} [Fintype I] (M : Matrix I I ℂ) (a b : I → ℂ) :
    star (a ⬝ᵥ M *ᵥ b) = star a ⬝ᵥ (Mᴴ)ᵀ *ᵥ star b := by
  simp only [dotProduct, mulVec, Finset.sum_apply, star_sum, star_mul', Pi.star_apply, transpose_apply,
    conjTranspose_apply, Finset.mul_sum, RCLike.star_def]

theorem im_tz_form {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) (hZ : Zᵀ = Z)
    (hP : (1 - Zᴴ * Z).PosDef) (z w : I → ℂ) :
    (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = Zᴴ := ⟨_, rfl⟩
  rw [← hBdef] at hP ⊢
  have hBt : Bᵀ = B := by
    rw [hBdef]; ext i j
    simp only [transpose_apply, conjTranspose_apply]
    rw [← transpose_apply Z i j, hZ]
  have hBh : Bᴴ = Z := by rw [hBdef, conjTranspose_conjTranspose]
  have hdet : IsUnit (1 - B * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
  obtain ⟨H, hHdef⟩ : ∃ H, H = (1 - B * Z)⁻¹ := ⟨_, rfl⟩
  rw [← hHdef]
  have h1 : H * (1 - B * Z) = 1 := by rw [hHdef]; exact Matrix.nonsing_inv_mul _ hdet
  have h2 : (1 - B * Z) * H = 1 := by rw [hHdef]; exact Matrix.mul_nonsing_inv _ hdet
  have hHh : Hᴴ = H := by rw [hHdef]; exact hP.inv.isHermitian.eq
  have hT : (1 - B * Z)ᵀ = 1 - Z * B := by
    rw [transpose_sub, transpose_one, transpose_mul, hZ, hBt]
  have h3 : Hᵀ * (1 - Z * B) = 1 := by
    have := congrArg transpose h2
    rwa [transpose_mul, hT, transpose_one] at this
  have h4 : (1 - Z * B) * Hᵀ = 1 := by
    have := congrArg transpose h1
    rwa [transpose_mul, hT, transpose_one] at this
  have c1 : B * (1 - Z * B) = (1 - B * Z) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have c2 : Z * (1 - B * Z) = (1 - Z * B) * Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have K : H * B = B * Hᵀ := by
    calc H * B = H * B * ((1 - Z * B) * Hᵀ) := by rw [h4, Matrix.mul_one]
      _ = H * (B * (1 - Z * B)) * Hᵀ := by simp only [Matrix.mul_assoc]
      _ = H * (1 - B * Z) * (B * Hᵀ) := by rw [c1]; simp only [Matrix.mul_assoc]
      _ = B * Hᵀ := by rw [h1, Matrix.one_mul]
  have K2 : Z * H = Hᵀ * Z := by
    calc Z * H = Hᵀ * (1 - Z * B) * (Z * H) := by rw [h3, Matrix.one_mul]
      _ = Hᵀ * ((1 - Z * B) * Z) * H := by simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z * ((1 - B * Z) * H) := by rw [← c2]; simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z := by rw [h2, Matrix.mul_one]
  have hHB : H = 1 + H * B * Z := by
    have : H * (1 - B * Z) = H - H * B * Z := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this] at h1
    rw [← h1]; abel
  have hs : star (tz Z w) = star w - B *ᵥ w := by
    unfold tz
    rw [star_sub, star_mulVec, star_star, ← hBdef, ← mulVec_transpose, hBt]
  have dz : ∀ y : I → ℂ, (Z *ᵥ star z) ⬝ᵥ y = star z ⬝ᵥ Z *ᵥ y := by
    intro y
    rw [dotProduct_mulVec (star z), ← mulVec_transpose, hZ]
  have e1 : z ⬝ᵥ H *ᵥ star w = z ⬝ᵥ star w + z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    conv_lhs => rw [hHB]
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have e2 : z ⬝ᵥ H *ᵥ B *ᵥ w = z ⬝ᵥ (H * B) *ᵥ w := by rw [mulVec_mulVec]
  have e3 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ star w = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [dz, mulVec_mulVec]
  have e4 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ B *ᵥ w = star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [dz, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have s3 : star (z ⬝ᵥ (H * B) *ᵥ w) = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, conjTranspose_mul, hBh, hHh, transpose_mul, hZ, ← K2]
  have s4 : star (star z ⬝ᵥ (Z * H * B) *ᵥ w) = z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, star_star, conjTranspose_mul, conjTranspose_mul, hBh, hHh, ← hBdef,
      transpose_mul, transpose_mul, hZ, hBt, ← K]
  have main : tz Z z ⬝ᵥ H *ᵥ star (tz Z w) = z ⬝ᵥ star w + star (star z ⬝ᵥ (Z * H * B) *ᵥ w)
      - z ⬝ᵥ (H * B) *ᵥ w - star (z ⬝ᵥ (H * B) *ᵥ w) + star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [hs, s3, s4]
    unfold tz
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e1, e2, e3, e4]
    ring
  rw [main]
  simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

theorem im_tz_form' : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im :=
  fun Z hZ hP z w => im_tz_form Z hZ hP z w

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginaryStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_transform_symplectic_imaginary : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.im_tz_form' <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspace
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspace
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames

variable {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' g : ℕ}

theorem span_single_eq_eigSp {ι : Type} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k)
    (s : 𝓞 E →+* ℂ) (f : ι → Fin g) (h1 : ∀ i, emb σ (e.symm (f i)) = s)
    (h2 : ∀ k, emb σ (e.symm k) = s → ∃ i, f i = k) :
    Submodule.span ℂ (Set.range fun i : ι => (Pi.single (f i) 1 : Fin g → ℂ)) = eigSp B s := by
  have hmem : ∀ x : Fin g → ℂ, x ∈ eigSp B s ↔ ∀ a, B a x = s a • x := by
    intro x
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (hmem _).2 fun a => ?_
    funext k
    rw [hB]
    by_cases hk : k = f i
    · subst hk
      simp [h1 i]
    · simp [Pi.single_eq_of_ne hk]
  · intro x hx
    have hx' := (hmem x).1 hx
    have hsum : x = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ) := by
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : x k = 0
    · simp [hk]
    · have hs : emb σ (e.symm k) = s := by
        ext a
        have h := congrFun (hx' a) k
        rw [hB, Pi.smul_apply, smul_eq_mul] at h
        exact mul_right_cancel₀ hk h
      obtain ⟨i, rfl⟩ := h2 k hs
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


omit [NumberField E] in
theorem conj_ne (σ : Ψ → (𝓞 E →+* ℂ)) (h : IsCMFam σ) (τ τ' : Ψ) : σ τ' ≠ (starRingEnd ℂ).comp (σ τ) :=
  fun hc => ((h.2 (σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hc⟩


omit [NumberField E] in
theorem conj_comp_inj {s t : 𝓞 E →+* ℂ} (h : (starRingEnd ℂ).comp s = (starRingEnd ℂ).comp t) : s = t := by
  ext a
  have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h a)
  simpa using this


omit [NumberField E] in
theorem conj_conj_comp (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem span_single_eigenspace [IsCMField E] [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hcm : IsCMFam σ) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k) (τ : Ψ) :
    Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧
      Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) =
        eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  constructor
  · refine span_single_eq_eigSp σ e B hB (σ τ) (fun i : Fin j' => e (Sum.inl i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · have h : σ τ' = σ τ := hk
        obtain rfl := hcm.1 h
        exact ⟨b, rfl⟩
      · have h : (starRingEnd ℂ).comp (σ τ') = σ τ := hk
        refine absurd ?_ (conj_ne σ hcm τ τ')
        rw [← h, conj_conj_comp]
  · refine span_single_eq_eigSp σ e B hB _ (fun i : Fin j => e (Sum.inr i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · exact absurd (show σ τ' = (starRingEnd ℂ).comp (σ τ) from hk) (conj_ne σ hcm τ τ')
      · have h : (starRingEnd ℂ).comp (σ τ') = (starRingEnd ℂ).comp (σ τ) := hk
        obtain rfl := hcm.1 (conj_comp_inj h)
        exact ⟨b, rfl⟩

theorem span_single_eigSp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) :=
  fun σ e B h hB τ => span_single_eigenspace σ e B h hB τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspaceStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_standard_basis_eigenspace : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotential
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotential
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot

theorem one_sub_bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    1 - (bigZ q t)ᴴ * bigZ q t = blockDiagonal fun τ =>
      fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0 (1 - ((ballMat q t τ)ᵀ)ᴴ * (ballMat q t τ)ᵀ) := by
  unfold bigZ
  rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
  congr 1
  funext τ
  rw [Pi.sub_apply, Pi.one_apply, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

theorem inv_blockDiagonal_fromBlocks {o a b : Type} [Fintype o] [DecidableEq o] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : o → Matrix a a ℂ) (D : o → Matrix b b ℂ)
    (hA : ∀ k, (A k).det ≠ 0) (hD : ∀ k, (D k).det ≠ 0) :
    (blockDiagonal fun k => fromBlocks (A k) 0 0 (D k))⁻¹ =
      blockDiagonal fun k => fromBlocks (A k)⁻¹ 0 0 (D k)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← blockDiagonal_mul, ← blockDiagonal_one]
  congr 1
  funext k
  rw [fromBlocks_multiply, Pi.one_apply, ← fromBlocks_one]
  have h1 : (A k)⁻¹ * A k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA k))
  have h2 : (D k)⁻¹ * D k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hD k))
  simp [h1, h2]

theorem det_conj_block {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (Z : Matrix b a ℂ) :
    (1 - (Zᵀ)ᴴ * Zᵀ).det = (1 - Zᴴ * Z).det := by
  rw [Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose (1 - Zᴴ * Z)]
  congr 1
  rw [transpose_sub, transpose_one, transpose_mul]
  congr 1

theorem inv_apply_inl {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ)
    (ht : t ∈ ballDom q) (τ : Ψ) (a b : Fin j') :
    (1 - (bigZ q t)ᴴ * bigZ q t)⁻¹ (Sum.inl a, τ) (Sum.inl b, τ) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹ : Matrix (Fin j') (Fin j') ℂ) a b := by
  have hA : ∀ k, (1 - (ballMat q t k)ᴴ * ballMat q t k).det ≠ 0 := fun k => (ht k).det_pos.ne'
  have hD : ∀ k, (1 - ((ballMat q t k)ᵀ)ᴴ * (ballMat q t k)ᵀ).det ≠ 0 := fun k => by
    rw [det_conj_block]; exact hA k
  rw [one_sub_bigZ, inv_blockDiagonal_fromBlocks _ _ hA hD]
  simp

theorem one_sub_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ = ((1 - (bigZ q t)ᴴ * bigZ q t)⁻¹).submatrix e.symm e.symm := by
  have h : 1 - (bigZe e q t)ᴴ * bigZe e q t = (1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    unfold bigZe
    have h1 : (1 : Matrix (Fin g) (Fin g) ℂ) = (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ).submatrix e.symm e.symm :=
      (submatrix_one_equiv e.symm).symm
    rw [conjTranspose_submatrix, submatrix_mul_equiv, h1]
    rfl
  rw [h, inv_submatrix_equiv]

theorem log_det_inv {a : Type} [Fintype a] [DecidableEq a] (A : Matrix a a ℂ) (hA : A.PosDef) :
    Real.log (A⁻¹).det.re = -Real.log A.det.re := by
  have hpos : 0 < A.det := hA.det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  have hreal : A.det = (A.det.re : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hinv : (A⁻¹).det = ((A.det.re)⁻¹ : ℝ) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hreal]
    simp
  rw [hinv, Complex.ofReal_re, Real.log_inv]

theorem logDet_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ) (ht : t ∈ ballDom q)
    (hH : R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹) :
    R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  unfold RiemLat.logDet ballPot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hG : R.gram (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)ᵀ := by
    ext a b
    have hs : star (Pi.single (e (Sum.inl a, τ)) 1 : Fin g → ℂ) = Pi.single (e (Sum.inl a, τ)) 1 := by
      ext i
      by_cases h : i = e (Sum.inl a, τ)
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, hs, transpose_apply]
    rw [Matrix.mulVec_single_one, single_one_dotProduct, hH, one_sub_bigZe]
    simp [inv_apply_inl q t ht]
  rw [hG, det_transpose, log_det_inv _ (ht τ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotentialStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eq_ball_potential : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ), t ∈ ballDom q → R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ → R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot.logDet_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def ipLin (R : RiemLat E g Λ) (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' y y' := by simp [RiemLat.ip, add_dotProduct]
  map_smul' c y := by simp [RiemLat.ip, smul_dotProduct]

theorem ip_eq_ipLin (R : RiemLat E g Λ) (x y : Fin g → ℂ) : R.ip x y = ipLin R x y := rfl

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def diagAct (s : Fin g → (𝓞 E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun x k => s k a * x k
      map_add' := fun x y => funext fun k => by simp [mul_add]
      map_smul' := fun r x => funext fun k => by simp [mul_left_comm] }
  map_one' := LinearMap.ext fun x => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun x => funext fun k => by simp [mul_assoc]
  map_zero' := LinearMap.ext fun x => funext fun k => by simp
  map_add' a b := LinearMap.ext fun x => funext fun k => by simp [add_mul]

theorem diagAct_apply (s : Fin g → (𝓞 E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (k : Fin g) :
    diagAct s a x k = s k a * x k := rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : RiemLat E g Λ) (e : ι ≃ Fin g) (c : ι → Fin g → ℂ)

include e

theorem sum_ip_smul (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (z : Fin g → ℂ) :
    ∑ i, R.ip (c i) z • c i = z := by
  have hli : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h := congrArg (ipLin R (c k)) ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h
    simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul] at h
    simpa using h
  have hspan : Submodule.span ℂ (Set.range c) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Fintype.card_congr e])
  have hz : z ∈ Submodule.span ℂ (Set.range c) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ip_eq_ipLin, map_sum]
  simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp

theorem sum_ip_mul_conj (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (u v : Fin g → ℂ) :
    ∑ i, R.ip (c i) u * starRingEnd ℂ (R.ip (c i) v) = R.ip v u := by
  conv_rhs => rw [← sum_ip_smul R e c hc u]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ip_eq_ipLin, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← ip_eq_ipLin, conj_ip, smul_eq_mul]

theorem ip_act (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (s : ι → (𝓞 E →+* ℂ))
    (hs : ∀ i, c i ∈ eigSp R.B (s i)) (a : 𝓞 E) (i : ι) (z : Fin g → ℂ) :
    R.ip (c i) (R.B a z) = s i a * R.ip (c i) z := by
  have hB : ∀ l, R.B a (c l) = s l a • c l := fun l => by
    have h := (Submodule.mem_iInf _).1 (hs l) a
    have h' := LinearMap.mem_ker.1 h
    simpa [sub_eq_zero] using h'
  conv_lhs => rw [← sum_ip_smul R e c hc z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ip_eq_ipLin, map_sum]
  simp only [map_smul, hB, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp [mul_comm]

end Frame

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' : ℕ}

theorem exists_riemLat_coord (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (c : Ix Ψ j j' → Fin g → ℂ) (hs : ∀ i, c i ∈ eigSp R₀.B (emb σ i))
    (hc : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) :
    ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x k => R₀.ip (c (e.symm k)) (R₀.P x)
      map_zero' := funext fun k => by simp [ip_eq_ipLin]
      map_add' := fun x y => funext fun k => by simp [ip_eq_ipLin] }
  have hP : ∀ x k, P x k = R₀.ip (c (e.symm k)) (R₀.P x) := fun _ _ => rfl
  refine ⟨{ free := R₀.free, fin := R₀.fin, rank := R₀.rank, form := R₀.form, alt := R₀.alt, unimod := R₀.unimod,
            adj := R₀.adj, P := P, Hm := 1, herm := isHermitian_one, pos := ?_, im := ?_,
            B := diagAct fun k => emb σ (e.symm k), act := ?_ }, rfl, rfl, fun _ _ _ => rfl⟩
  · intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have hk' : z k ≠ 0 := hk
    have : (z ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star z).re = ∑ l, Complex.normSq (z l) := by
      simp [dotProduct, Complex.mul_conj]
    rw [this]
    exact Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hk'⟩
  · intro x y
    have key : P x ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (P y) = R₀.P x ⬝ᵥ R₀.Hm *ᵥ star (R₀.P y) := by
      have h := sum_ip_mul_conj R₀ e c hc (R₀.P x) (R₀.P y)
      rw [← e.symm.sum_comp] at h
      rw [one_mulVec]
      exact h
    rw [key]
    exact R₀.im x y
  · intro a x
    funext k
    rw [diagAct_apply, hP, hP, R₀.act]
    exact ip_act R₀ e c hc (emb σ) hs a (e.symm k) (R₀.P x)

theorem coord_lat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k :=
  fun R₀ σ e c hs hc => exists_riemLat_coord R₀ σ e c hs hc

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLatticeStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalized_riemann_lattice : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat.coord_lat <;> assumption)
end
end

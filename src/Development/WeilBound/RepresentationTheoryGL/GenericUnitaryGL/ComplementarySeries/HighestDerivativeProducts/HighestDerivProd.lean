module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerOfFibIntEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRightInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLevi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLevi
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

theorem map_smInt_translate {X Z Z' : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (μ : MeasureTheory.Measure X) [μ.IsAddHaarMeasure]
    (L : Z →ₗ[ℂ] Z') (T : Z →ₗ[ℂ] Z) (hT : ∀ z, L (T z) = L z) (φ : X → Z) (m : X)
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    L (smInt μ (fun v => T (φ (v + m)))) = L (smInt μ φ) := by
  obtain ⟨_, h2, h3, _⟩ := SmIntEl.smInt_properties (X := X) (W := Z) (W' := Z) μ
  have hl' : IsLocallyConstant (φ ∘ fun v => v + m) := hl.comp_continuous ((continuous_id.add continuous_const))
  have hc' : HasCompactSupport (φ ∘ fun v => v + m) :=
    hc.comp_homeomorph (Homeomorph.addRight m)
  have e1 : smInt μ (T ∘ (φ ∘ fun v => v + m)) = T (smInt μ (φ ∘ fun v => v + m)) := h2 T _ hl' hc'
  have e2 : smInt μ (φ ∘ fun v => v + m) = smInt μ φ :=
    h3 (fun v => v + m) φ (MeasureTheory.measurePreserving_add_right μ m) hl
  calc L (smInt μ (fun v => T (φ (v + m)))) = L (T (smInt μ (φ ∘ fun v => v + m))) :=
        congrArg L e1
    _ = L (smInt μ (φ ∘ fun v => v + m)) := hT _
    _ = L (smInt μ φ) := congrArg L e2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem midV_add (i t : ℕ) (v m : Fin t → k) :
    midV k i t (v + m) = midV k i t v + midV k i t m := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem mul_uM_eq (i t : ℕ) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y =
      uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g) := by
  have e : midV k i t v + (topV k i t x + midV k i t m) = topV k i t x + midV k i t (v + m) := by
    rw [midV_add]; abel
  rw [mul_assoc, levi_mul_uM, hy, ← mul_assoc, ← uM_add, e, uM_add, mul_assoc]

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin i → k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (uM k i x, 1) z) = clT τ W z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b =>
    have hq : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) a) = (twKer τ (MirUin k i) 1).mkQ a := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨_, uM_mem k i x⟩, a, ?_⟩)
      simp
    rw [extTensor_tmul]
    simp only [clT, LinearMap.rTensor_tmul, map_one, Module.End.one_apply]
    exact congrArg (· ⊗ₜ[ℂ] b) hq


set_option maxHeartbeats 1000000 in
theorem fibV_prodPG (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (y : Fin (i + t) → k)
    (x : Fin i → k) (m v : Fin t → k)
    (hy : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibV (prodPG τ σ (uM k (i + t) y) f) g v = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) := by
  refine Exists.elim (GlobalTheory.T.unipotent_top_mem_parabolic k i t x) fun hmem hproj => ?_
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) g v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g * uM k (i + t) y) := rfl
  have e2 := f.1.1.2 ⟨_, hmem⟩ (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)
  calc fibV (prodPG τ σ (uM k (i + t) y) f) g v
      = f.1.1.1 (uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t (v + m)) * levi k (i + t) g)) :=
        e1.trans (congrArg f.1.1.1 (mul_uM_eq i t g y x m v hy))
    _ = extTensor τ σ (pgProj k i t ⟨_, hmem⟩) (fibV f g (v + m)) := e2
    _ = extTensor τ σ (uM k i x, 1) (fibV f g (v + m)) :=
        congrArg (fun a => extTensor τ σ a (fibV f g (v + m))) hproj

theorem fibInt_col (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (x : Fin i → k) (m : Fin t → k)
    (hxm : (g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t m) :
    fibInt μ (prodPG τ σ (uM k (i + t) y) f) g = fibInt μ f g := by
  have hlc := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hfun : fibV (prodPG τ σ (uM k (i + t) y) f) g =
      fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m)) :=
    funext fun v => fibV_prodPG τ σ f g y x m v hxm
  have h1 : clT τ W (smInt μ (fibV (prodPG τ σ (uM k (i + t) y) f) g)) =
      clT τ W (smInt μ fun v => (extTensor τ σ (uM k i x, 1)) (fibV f g (v + m))) :=
    congrArg (fun φ => clT τ W (smInt μ φ)) hfun
  exact h1.trans (map_smInt_translate μ (clT τ W) (extTensor τ σ (uM k i x, 1))
          (clT_extTensor τ σ x) (fibV f g) m hlc.1 hlc.2)


set_option maxHeartbeats 1000000 in
theorem fibInt_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f u hu g
  refine Exists.elim (exists_uM_of_mem k (i + t) hu) fun y hy => ?_
  refine Exists.elim (exists_top_mid k i t ((g : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)) fun x hx => ?_
  refine Exists.elim hx fun m hxm => ?_
  exact (congrArg (fun u' => fibInt μ (prodPG τ σ u' f) g) hy).trans
    (fibInt_col τ σ hτ hσ μ f y g x m hxm)

end GlobalTheory.CompanionTheory.BZPsiPG.FibUnip

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLeviStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_intertwines_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (u : Mir k (i + t)), u ∈ MirUin k (i + t) → ∀ g : GL (Fin (i + t)) k, fibInt μ (prodPG τ σ u f) g = fibInt μ f g := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | exact GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibUnip.fibInt_unip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIsoStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Norm

section Generic

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def twistEquivOf {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (GlobalTheory.SmGL.twist ρ χ).Equiv (GlobalTheory.SmGL.twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (φ.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (φ.isIntertwining' g) v)

def pairT (a : V) (y : W) : ∀ x : Bool, TwoT V W x
  | false => a
  | true => y

theorem bool_tprod_pairT (a : V) (y : W) :
    Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ (pairT a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] W) :=
  Exponents.boolTensorEquiv_tprod _

theorem tprod_pairT_smul (a : V) (c d : ℂ) (y : W) :
    PiTensorProduct.tprod ℂ (pairT (c • a) (d • y)) = (c * d) • PiTensorProduct.tprod ℂ (pairT a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V W)).injective
  rw [map_smul, bool_tprod_pairT, bool_tprod_pairT]
  exact TensorProduct.smul_tmul_smul c d a y

end Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

theorem det_levi' (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

theorem dpowM_levi' (n : ℕ) (s : ℝ) (g : GL (Fin n) k) : dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi']

theorem dpowM_of_mem' (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip', map_one]

theorem scalar_sum (i t : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * (absPow k 1 b * (absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) a *
        absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) b)) =
      absPow k ((t : ℂ) / 2) a * absPow k (-(i : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) a := by
  have e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    ring
  have e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg, ← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e0, e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((t : ℂ) / 2) a = T
  generalize absPow k (-(i : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (B * B * (T * (R * B⁻¹))) = (B⁻¹ * B) * (B * B⁻¹) * (T * R * A⁻¹) := by ac_rfl
    _ = T * R * A⁻¹ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem twKer_twist_dpowM {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (τ : Representation ℂ (Mir k n) V) (s : ℝ) :
    twKer (GlobalTheory.SmGL.twist τ (dpowM n s)) (MirUin k n) 1 = twKer τ (MirUin k n) 1 := by
  unfold twKer
  congr 1
  ext w
  refine exists_congr fun u => exists_congr fun v => ?_
  have hu : dpowM n s (u : Mir k n) = 1 := dpowM_of_mem' n s u.1 u.2
  rw [twist_apply, hu, Units.val_one, one_smul]

end Chars

section Main

variable {i t : ℕ} (τ : MRep k i) (σ : GRep k t)

abbrev eIT (i t : ℕ) : (Σ x, Two (Fin i) (Fin t) x) ≃ Fin (i + t) := two (stdSum (rfl : i + t = i + t))

abbrev sigT : Representation ℂ (Qp k i t) (PiTensorProduct ℂ (TwoT (psiN τ).V σ.V)) :=
  (GlobalTheory.SmGL.twist (piTensor (twoRep (psiN τ).ρ σ.ρ)) (deltaHalf k (Two (Fin i) (Fin t)))).comp (leviProj k (eIT i t))

abbrev mkT (s : ℝ) : τ.V →ₗ[ℂ] Jacquet (mtw τ s).ρ (MirUin k i) := (twKer (mtw τ s).ρ (MirUin k i) 1).mkQ

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k i) 1).mkQ

def Lq (s : ℝ) : (Jacquet (mtw τ s).ρ (MirUin k i) ⊗[ℂ] σ.V) ≃ₗ[ℂ] PiTensorProduct ℂ (TwoT (psiN τ).V σ.V) :=
  (TensorProduct.congr (Submodule.quotEquivOfEq _ _ (twKer_twist_dpowM i τ.ρ s)) (LinearEquiv.refl ℂ σ.V)).trans
    (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).symm

theorem Lq_tmul (s : ℝ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s y ⊗ₜ[ℂ] w) = PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective
  rw [bool_tprod_pairT]
  refine (LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_
  rfl

theorem qRep_tmul (s₁ s₂ : ℝ) (q : Qp k i t) (y : τ.V) (w : σ.V) :
    qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) •
        (mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)) := by
  have h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V) := by
    refine (extTensor_tmul _ _ _ _ _).trans ?_
    show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _
    rw [dpowM_levi']
    rfl
  exact congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h

theorem Lq_tmul_smul (s : ℝ) (c d : ℂ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s (c • y) ⊗ₜ[ℂ] (d • w : σ.V)) = (c * d) • PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  rw [Lq_tmul, map_smul, tprod_pairT_smul]

theorem scalar_q (i t : ℕ) (q : Qp k i t) :
    ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) *
        (((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) *
          (((dpow i (((t : ℕ) : ℝ) / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) *
            ((dpow t (-((i + 1 : ℕ) : ℝ) / 2) (qBlocks k i t q).2 : ℂˣ) : ℂ))) =
      ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) *
        ((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) := by
  have hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q) := by
    funext x
    cases x
    · rfl
    · rfl
  have hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) =
      GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2 := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
    rfl
  rw [hlev, deltaHalf_two]
  simp only [← Units.val_mul]
  congr 1
  have := scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1)
    (GeneralLinearGroup.det (qBlocks k i t q).2)
  simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
  exact this

def qEnd (s₁ s₂ : ℝ) (q : Qp k i t) :
    (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) →ₗ[ℂ] (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) :=
  qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q

theorem sigT_Lq (q : Qp k i t) (v : Jacquet (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (MirUin k i) ⊗[ℂ] σ.V) :
    sigT τ σ q (Lq τ σ (((t : ℕ) : ℝ) / 2) v) =
      ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) •
        Lq τ σ (((t : ℕ) : ℝ) / 2) (qEnd τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul x w =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) =
        pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y))
          ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w) := by
      funext x
      cases x
      · rfl
      · exact (one_smul ℂ _).symm
    have hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) =
        ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
          (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) •
            PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (qBlocks k i t q).2 w)) := by
      show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
        piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _
      rw [piTensor_tprod]
      exact congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))
    have hR := qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w
    refine (congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)
    refine Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)
    show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)
    rw [map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]
    congr 1
    rw [← scalar_q i t q]
    ring

end Main

theorem psiN_prodPGn_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  intro k _ _ _ _ i t τ σ _ _ hE
  obtain ⟨E⟩ := hE
  exact ⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans
    (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Norm

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_of_product_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | exact GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Norm.psiN_prodPGn_of_equiv <;> assumption)
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM
noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.BZPsiPG.Hand
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibInt_levi (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g' g : GL (Fin (i + t)) k) :
    fibInt μ (prodPG τ σ (levi k (i + t) g') f) g = fibInt μ f (g * g') := by
  have : fibV (prodPG τ σ (levi k (i + t) g') f) g = fibV f (g * g') := by
    funext v
    have e : uM k (i + t) (midV k i t v) * levi k (i + t) (g * g') =
        uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) g' := by
      rw [map_mul, mul_assoc]
    exact (congrArg f.1.1.1 e).symm
  exact congrArg (fun x => clT τ W (smInt μ x)) this

theorem isOpen_stab_of {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G Z) (z : Z) (S : Set G) (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ s ∈ S, ρ s z = z) :
    IsOpen {g : G | ρ g z = z} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have ho : IsOpen ((fun y => g⁻¹ * y) ⁻¹' S) := hS.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun y hy => ?_
  have e := h _ hy
  show ρ y z = z
  have : y = g * (g⁻¹ * y) := by group
  rw [this, map_mul, Module.End.mul_apply, e]
  exact hg

theorem isOpen_cInd_stab {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) : IsOpen {p | prodPG τ σ p f = f} := by
  have h : IsOpen {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := f.1.2
  have e : {p | prodPG τ σ p f = f} = {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := by
    ext p
    constructor
    · intro e
      exact congrArg (fun x : cIndSpace (HPG k i t) (hRep τ σ) => x.1.1) e
    · intro e
      exact Subtype.ext (Subtype.ext e)
  rw [e]
  exact h

section Map
variable (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
  [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]

include hτ hσ

theorem fibInt_add (a b : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (a + b) g = fibInt μ a g + fibInt μ b g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  obtain ⟨b1, b2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ b g
  have e : fibV (a + b) g = fibV a g + fibV b g := by
    funext v
    exact map_add (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a b
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).1 _ _ a1 a2 b1 b2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_add _ _ _))

theorem fibInt_smul (c : ℂ) (a : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (c • a) g = c • fibInt μ a g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  have e : fibV (c • a) g = ((c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W)) ∘ fibV a g := by
    funext v
    exact map_smul (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) c a
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.1
    (c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) _ a1 a2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_smul (clT τ W) c _))

def phiInd (f : cIndSpace (HPG k i t) (hRep τ σ)) : indSpace (Qp k i t) (qRep τ σ) :=
  ⟨fibInt μ f, fun q g => GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g⟩

theorem phiInd_right (f : cIndSpace (HPG k i t) (hRep τ σ)) (s : GL (Fin (i + t)) k)
    (hs : prodPG τ σ (levi k (i + t) s) f = f) :
    ind (Qp k i t) (qRep τ σ) s (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f := by
  apply Subtype.ext
  funext g
  exact (fibInt_levi τ σ μ f s g).symm.trans (congrArg (fun x => fibInt μ x g) hs)

theorem phiInd_mem (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    phiInd τ σ hτ hσ μ f ∈ smoothPart (ind (Qp k i t) (qRep τ σ)) := by
  have h : IsOpen {g | ind (Qp k i t) (qRep τ σ) g (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f} :=
    isOpen_stab_of (ind (Qp k i t) (qRep τ σ)) _
      (levi k (i + t) ⁻¹' {p | prodPG τ σ p f = f})
      ((isOpen_cInd_stab f).preimage (GlobalTheory.T.continuous_levi_unipotent_proj k _).1)
      (by
        have h0 : levi k (i + t) (1 : GL (Fin (i + t)) k) = 1 := (levi k (i + t)).map_one
        have h1 : prodPG τ σ (1 : Mir k (i + t)) = 1 := (prodPG τ σ).map_one
        exact (congrArg (fun x => prodPG τ σ x f) h0).trans (LinearMap.congr_fun h1 f))
      (fun s hs => phiInd_right τ σ hτ hσ μ f s hs)
  exact h

def phiFun (f : cIndSpace (HPG k i t) (hRep τ σ)) : smoothPart (ind (Qp k i t) (qRep τ σ)) :=
  ⟨phiInd τ σ hτ hσ μ f, phiInd_mem τ σ hτ hσ μ f⟩

def phiLin : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] smoothPart (ind (Qp k i t) (qRep τ σ)) where
  toFun := phiFun τ σ hτ hσ μ
  map_add' a b := Subtype.ext (Subtype.ext (funext fun g => fibInt_add τ σ hτ hσ μ a b g))
  map_smul' c a := Subtype.ext (Subtype.ext (funext fun g => fibInt_smul τ σ hτ hσ μ c a g))

theorem phiLin_apply (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    (phiLin τ σ hτ hσ μ f).1.1 g = fibInt μ f g := rfl

theorem twKer_le_ker : twKer (prodPG τ σ) (MirUin k (i + t)) 1 ≤ LinearMap.ker (phiLin τ σ hτ hσ μ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, w, rfl⟩
  have e : phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w) = phiLin τ σ hτ hσ μ w :=
    Subtype.ext (Subtype.ext (funext fun g => GlobalTheory.T.fibre_integral_intertwines_levi k i t τ σ hτ hσ μ w (u : Mir k (i + t)) u.2 g))
  have e2 : (((1 : MirUin k (i + t) →* ℂˣ) u : ℂˣ) : ℂ) • w = w := by simp
  show phiLin τ σ hτ hσ μ _ = 0
  exact (congrArg (fun x => phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w - x)) e2).trans
    ((map_sub (phiLin τ σ hτ hσ μ) _ _).trans (sub_eq_zero.2 e))

theorem ker_le_twKer : LinearMap.ker (phiLin τ σ hτ hσ μ) ≤ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro f hf
  have h : phiLin τ σ hτ hσ μ f = 0 := hf
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero k i t τ σ hτ hσ μ f fun g => congrFun (congrArg (fun x : smoothPart (ind (Qp k i t) (qRep τ σ)) => x.1.1) h) g

theorem phiLin_surj : Function.Surjective (phiLin τ σ hτ hσ μ) := by
  intro G
  have h := GlobalTheory.CompanionTheory.BZPsiPG.exists_fibInt_eq k i t τ σ hτ hσ μ G
  refine h.imp fun f hf => ?_
  have e : (phiLin τ σ hτ hσ μ f).1.1 = G.1.1 := funext fun g => (phiLin_apply τ σ hτ hσ μ f g).trans (hf g)
  exact Subtype.ext (Subtype.ext e)

theorem phiLin_levi (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    phiLin τ σ hτ hσ μ (prodPG τ σ (levi k (i + t) g) f) = smInd (Qp k i t) (qRep τ σ) g (phiLin τ σ hτ hσ μ f) :=
  Subtype.ext (Subtype.ext (funext fun x => fibInt_levi τ σ μ f g x))

end Map

theorem twAct_equiv_of_map {G M Z Z' : Type} [Group G] [Group M] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (ρ : Representation ℂ G Z) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (ρ' : Representation ℂ M Z')
    (Φ : Z →ₗ[ℂ] Z') (hk : LinearMap.ker Φ = twKer ρ N θ) (hsurj : Function.Surjective Φ)
    (hint : ∀ m z, Φ (ρ (s m) z) = ρ' m (Φ z)) :
    Nonempty ((twAct ρ N θ s hs).Equiv ρ') := by
  let e : TwJacquet ρ N θ ≃ₗ[ℂ] Z' :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  refine ⟨.mk e fun g => ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hint g f

theorem core (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ) :
    Nonempty ((psiMinus k (prodPG τ σ)).Equiv (smInd (Qp k i t) (qRep τ σ))) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  exact twAct_equiv_of_map (prodPG τ σ) (MirUin k (i + t)) 1 (levi k (i + t)) (levi_normalises (i + t))
    (smInd (Qp k i t) (qRep τ σ)) (phiLin τ σ hτ hσ (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin t → k)))
    (le_antisymm (ker_le_twKer τ σ hτ hσ _) (twKer_le_ker τ σ hτ hσ _))
    (phiLin_surj τ σ hτ hσ _) (fun g f => phiLin_levi τ σ hτ hσ _ f g)

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isSmoothChar_dpowM (n : ℕ) (s : ℝ) : IsSmoothChar (dpowM (k := k) n s) :=
  (isSmoothChar_dpow (n + 1) s).comp _ continuous_subtype_val

theorem psiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiPG k := by
  intro k _ _ _ _ i t τ σ hτ hσ
  exact GlobalTheory.T.derivative_of_product_induced_iso k i t τ σ hτ hσ
    (core _ _ (isSmooth_twist hτ (isSmoothChar_dpowM _ _)) (isSmooth_twist hσ (isSmoothChar_dpow _ _)))

end GlobalTheory.CompanionTheory.BZPsiPG.Hand
end
end

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  GlobalTheory.T.leibniz_order_of_exact_sequences k (GlobalTheory.T.residue_sequence_holds k) (GlobalTheory.T.psi_gp_commutation_holds k) (GlobalTheory.T.phi_gp_commutation_holds k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand

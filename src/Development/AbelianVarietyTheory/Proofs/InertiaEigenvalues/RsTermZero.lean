module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachOperatorProductShiftMemLatticeStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionInvariantClause
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ
open scoped ComplexConjugate

namespace GlobalTheory.ZEul


open Classical in
def rsTerm (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

theorem rsTerm_zero (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) : rsTerm q α β x 0 = 1 := by
  have h : (fun _ : Fin n => (0 : ℕ)) = fun i => ((0 : Fin n → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) α = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def lastRow (g : GA E (m + 1)) : Fin (m + 1) → Ad E := fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j

def uInt (φ φ' : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℂ :=
  whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i))) *
    conj (whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i)))) *
    Φ (fun i => pInf E (lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (lastRow g i)) * (detPow E (m + 1) x g : ℂ)

end GlobalTheory.ZEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
noncomputable section

namespace GlobalTheory.SmGL.DepthZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.StepData ValuativeRel
open scoped TensorProduct

section Tensor

variable {α : Type} [Fintype α] [dec : DecidableEq α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def contract (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) : (⨂[ℂ] b, X b) →ₗ[ℂ] X a := GlobalTheory.MultilinearContraction.contract φ a

theorem contract_tprod (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (x : ∀ b, X b) :
    contract φ a (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a :=
  GlobalTheory.MultilinearContraction.contract_tprod φ a x

theorem exists_contract_ne_zero {w : ⨂[ℂ] b, X b} (hw : w ≠ 0) (a : α) :
    ∃ φ : ∀ a, X a →ₗ[ℂ] ℂ, contract φ a w ≠ 0 := by
  let b := fun i => Module.Free.chooseBasis ℂ (X i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr w p ≠ 0 := by
    by_contra! h
    exact hw (B.repr.injective (by ext p; simp [h p]))
  refine ⟨fun i => (b i).coord (p i), fun h => hp ?_⟩
  have key : (b a).coord (p a) ∘ₗ contract (fun i => (b i).coord (p i)) a = B.coord p := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contract_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have := congrArg (fun L => L w) key
  simp only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] at this
  exact this.symm

theorem contract_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (g : Γ a) (w : ⨂[ℂ] b, X b) :
    contract φ a (piTensor ρ (Pi.mulSingle a g) w) = ρ a g (contract φ a w) := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contract_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun b hb => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb)]; simp

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne₁ : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne₁ {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w⁻¹ * g * w ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w⁻¹ * g * w).val - 1 = (w⁻¹).val * (g.val - 1) * w.val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).2.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).1

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem leviEmb_mem_KOne₁ (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) :
    leviEmb k e g ∈ KOne k n := by
  refine mem_KOne.2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := mem_KOne.1 (hg a) i j
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  · have h' : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (e.injective h'))
    simp [Matrix.sub_apply, leviEmb_apply_ne k e g h, Matrix.one_apply_ne h']

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => tame_det_of_mem_KOne (fun x hx => isUnram_absPow k _ x ?_) (hg a)
  simpa using Valuation.map_one_add_of_lt _ hx

theorem exists_fixed_of_parInd (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KOne k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KOne k (m a)) → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨_, conj_mem_KOne₁ hc (leviEmb_mem_KOne₁ e hg)⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem fixed_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KOne k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KOne k (m a)), v ≠ 0 := by
  obtain ⟨S, F, hF⟩ := h
  obtain ⟨v, hv, hv0⟩ := hv
  obtain ⟨u, rfl⟩ := hF v
  have hS : IsSmooth S.toRepresentation := fun y => by
    have := isSmooth_parInd e (piTensor σ) y.1
    convert this using 3 with g
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hS isCompact_KOne₁ F.toLinearMap u fun g hg => by
    have h1 := hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact (F.isIntertwining _ _ g u).trans h1
  have hy0 : y.1 ≠ 0 := fun h => hv0 (by
    have : y = 0 := Subtype.ext h
    rw [this, map_zero] at hyu
    exact hyu.symm)
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd e (piTensor σ) (f := y.1)
    (fun g => congrArg Subtype.val (hy g)) hy0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine ⟨_, fun g => ?_, hφ⟩
  rw [← contract_piTensor, hw _ fun b => ?_]
  · simp
  · by_cases hb : b = a
    · subst hb; simp
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end GlobalTheory.SmGL.DepthZero

namespace GlobalTheory.SmGL

open GlobalTheory.PRep GlobalTheory.SplitRead

theorem depthZeroSupport : GlobalTheory.Published.DepthZeroSupport := by
  intro k _ _ _ _ n π s d σ h hv a
  obtain ⟨-, -, e, he⟩ := h
  exact DepthZero.fixed_of_isSubquotient e (fun a => (σ a).π) he hv a

end GlobalTheory.SmGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links

namespace GlobalTheory.LowestKType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def kop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def sop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def Cpt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Prop :=
  ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ)

def IsHarm (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (i l : Fin m), w.p τ ≤ (i : ℕ) → (l : ℕ) < w.p τ → kop w τ i l P = 0

def IsKHw (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a P = c • P

def IsKHwMap {W : Type} [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
    (ψ : W →ₗ[ℂ] PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b ∘ₗ ψ = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a ∘ₗ ψ = c • ψ

def IsNHw (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → sop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin n), sop w τ a a P = lam τ a • P

end GlobalTheory.LowestKType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}



open NumberField Matrix GlobalTheory.MirTower in
theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last


open NumberField Matrix GlobalTheory.MirTower in
theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolicStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.MirTower
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_series_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.lintegral_theta_unfold | exact GlobalTheory.ThetaUnfold.lintegral_theta_unfold | (intros; apply GlobalTheory.ThetaUnfold.lintegral_theta_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.IwahoriFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [Fintype n] in
theorem one_same (e : (Σ a, m a) ≃ n) (a : α) (i j : m a) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j := by
  simp [Matrix.one_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem one_ne (e : (Σ a, m a) ≃ n) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 :=
  Matrix.one_apply_ne fun e' => h (congrArg Sigma.fst (e.injective e'))

theorem exists_jPlus_mul_KOne (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x := by
  obtain ⟨h1, h3⟩ := mem_proRad.1 hg
  obtain ⟨h1, h2⟩ := mem_parahoric.1 h1
  let U : Matrix n n k := Matrix.of fun i j => if blk e i < blk e j then g.val i j else (1 : Matrix n n k) i j
  have hU : StepData.MaxM (U - g.val) := by
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [U, Matrix.sub_apply, Matrix.of_apply, blk_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · rw [if_neg (lt_irrefl a), one_same, Valuation.map_sub_swap]
      exact h3 a i j
    · rw [if_neg h.not_gt, one_ne e h.ne', zero_sub, Valuation.map_neg]
      exact h2 a b i j h
  obtain ⟨x, hx, hgx⟩ := StepData.exists_mul_KOne h1 hU
  refine ⟨g * x, ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j h => ?_, fun a i j => ?_⟩,
    mul_mem h1 (StepData.KOne_le_KO hx)⟩, x⁻¹, inv_mem hx, by simp⟩
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg h.not_gt, one_ne e h.ne']
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg (lt_irrefl a), one_same]

theorem exists_KOne_mul_jPlus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  exact ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hu.2) x).1 hx, u, hu, by simp⟩

theorem proRad_eq_sup (e : (Σ a, m a) ≃ n) : proRad k e = KOne k n ⊔ jPlus k e := by
  refine le_antisymm (fun g hg => ?_) (sup_le (KOne_le_proRad e) (jPlus_le_proRad e))
  obtain ⟨x, hx, u, hu, rfl⟩ := exists_KOne_mul_jPlus e hg
  exact Subgroup.mul_mem_sup hx hu

theorem exists_mul_mem_parab (e : (Σ a, m a) ≃ n) {x : GL n k} (hx : x ∈ KOne k n) :
    ∃ c ∈ jMinus k e, x * c ∈ parab k e := by
  have hx' := StepData.mem_KOne.1 hx
  have hA : ∀ a : α, ∃ y ∈ KOne k n, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix n n k) i l := fun a =>
    StepData.exists_mem_KOne fun i l => by
      simp only [Matrix.sub_apply, Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := StepData.exists_mem_KOne (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => StepData.mem_KOne.1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix n n k) i l) * c.val l j =
      (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix n n k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩, hc⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem exists_jLevi_mul_jPlus (e : (Σ a, m a) ≃ n) {p : GL n k} (hp : p ∈ parab k e) (h : p ∈ KOne k n) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, p = d * u := by
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k e ⟨p, hp⟩
  have hd : leviEmb k e (leviProj k e ⟨p, hp⟩) ∈ jLevi k e :=
    ⟨_, fun a _ => StepData.mem_KOne.2 fun i j => by
      have := StepData.mem_KOne.1 h (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at this
      exact this, rfl⟩
  refine ⟨_, hd, u, ⟨hu, ?_⟩, hpu⟩
  rw [(inv_mul_eq_iff_eq_mul.2 hpu).symm]
  exact StepData.KOne_le_KO (mul_mem (inv_mem (jLevi_le_KOne e hd)) h)

theorem conj_mem_jPlus (e : (Σ a, m a) ≃ n) {d u : GL n k} (hd : d ∈ jLevi k e) (hu : u ∈ jPlus k e) :
    d * u * d⁻¹ ∈ jPlus k e := by
  have h := StepData.KOne_le_KO (jLevi_le_KOne e hd)
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e g) u).1 hu.1,
    (KO k n).mul_mem ((KO k n).mul_mem h hu.2) ((KO k n).inv_mem h)⟩

theorem plus_levi_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab e hx
  obtain ⟨d, hd, v, hv, h⟩ := exists_jLevi_mul_jPlus e hp (mul_mem hx hc.2)
  refine ⟨_, mul_mem hu (conj_mem_jPlus e hd hv), d, hd, c⁻¹, inv_mem hc, ?_⟩
  rw [eq_mul_inv_of_mul_eq h]
  group

theorem levi_plus_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨d, hd, _, conj_mem_jPlus e (inv_mem hd) hu, c, hc, by group⟩

end GlobalTheory.LocGL.IwahoriFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

open GlobalTheory.SignedHC

theorem e_add_v_two_pos {R : Ranks} (P : HCParam R) (s ga : ℕ) (c : ℕ → ℤ) (j : Fin R.m) :
    0 < P.e j + ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
  obtain ⟨hv, hb, -⟩ := GridData.ofHCParam_spec P s ga c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 : (GridData.ofHCParam P s ga c).v (R.k - 2 + 2) < (GridData.ofHCParam P s ga c).v 2 :=
    (GridData.ofHCParam P s ga c).v_anti 2 _ le_rfl (by omega) (show R.k - 2 + 2 ≤ R.k by omega)
  have h2 : (GridData.ofHCParam P s ga c).b (0 + 1) ≤ (GridData.ofHCParam P s ga c).b (j.1 + 1) := by
    rcases Nat.eq_zero_or_pos j.1 with h | h
    · rw [h]
    · exact ((GridData.ofHCParam P s ga c).b_mono _ _ le_rfl (by omega) (show j.1 + 1 ≤ R.m from j.2)).le
  have h1' : P.v ⟨R.k - 2, by omega⟩ < ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
    rw [hv]; exact_mod_cast h1
  have h2' : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rw [hb, hb]; exact_mod_cast h2
  have h3 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h4 := P.u_last_gt (by omega) (by omega)
  have h5 : P.u ⟨R.k - 2 + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := by
    congr 2; omega
  have h6 := P.gap_be j
  have h7 : (0 : ℚ) ≤ R.t := by positivity
  simp only at h3
  linarith

theorem nFun_eq_bigN (D : D7) : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.Grid.bigN D := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h : Odd (D.R.r + 6) := by
    rw [Nat.odd_iff]; unfold Ranks.r; omega
  simp only [BlochKatoReduction.Gen.NFun, BlochKatoReduction.Gen.sFun, if_pos h, GlobalTheory.Grid.bigN, GlobalTheory.Grid.sLen]

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem qp_isUnit (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨wq, hwq⟩ := hR9.qq
  have h1 : IsUnit (algebraMap (LetA O n) W.EE (W.φA letπ)) := by
    have := W.EE_π.map W.φE
    rw [W.φE_ext] at this
    exact this
  rw [W.φA_π, map_mul] at h1
  have h2 := (IsUnit.mul_iff.1 h1).2
  rw [hwq, map_mul] at h2
  exact (IsUnit.mul_iff.1 h2).2

theorem qp_pow_inj (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) (k : ℕ) {x : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = 0) : x = 0 := by
  have hu := (qp_isUnit W hR9).pow k
  rw [← map_pow] at hu
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x] at h
  exact hu.smul_left_cancel.1 (h.trans (smul_zero _).symm)

theorem dl_of_qp (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) {i : ZMod n} {y : ℕ} {z : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.qp W ^ y • z)) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := by
  obtain ⟨hNΔ, hl⟩ := h
  have hN : Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := hNΔ.1
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) = Formalism.MainNotions.LiftingTheory.qp W ^ y • z := hNΔ.2
  obtain ⟨m, -, hme⟩ := Submodule.mem_map.1 hl
  refine ⟨⟨?_, fun δ hδ => ?_⟩, hN⟩
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ y) (letE i : LetA O n) z, ← hme]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self, sub_self]
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    have hq : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ y) = Formalism.MainNotions.LiftingTheory.qp W ^ y :=
      (W.AΔ.pow_mem (Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.qp_mem hR9) y) δ hδ
    have e : Formalism.MainNotions.LiftingTheory.qp W ^ y • W.γD T δ z = W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) := by
      rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, hq]
    rw [smul_sub, e, hΔ δ hδ, sub_self]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

def pseq (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ) : W.DD T :=
  Polynomial.aeval dop (((xs.take k).map fun x => Polynomial.X - Polynomial.C (cc x)).prod) z

theorem pseq_zero (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) :
    pseq W dop cc xs z 0 = z := by
  simp [pseq]

theorem pseq_succ (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ)
    (hk : k < xs.length) :
    pseq W dop cc xs z (k + 1) = dop (pseq W dop cc xs z k) - cc (xs.getD k 0) • pseq W dop cc xs z k := by
  have ht : xs.take (k + 1) = xs.take k ++ [xs.getD k 0] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    rfl
  unfold pseq
  rw [ht, List.map_append, List.prod_append, mul_comm, map_mul, Module.End.mul_apply]
  simp [Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem pseq_length (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (X : Finset ℤ) (z : W.DD T) :
    pseq W dop cc X.toList z X.toList.length =
      Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z := by
  unfold pseq
  rw [List.take_length, Finset.prod_map_toList]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem eigenvalue_product_maps_letter_lattice_local (l : ℕ) (hpl : PD.p = l)
    (hR9 : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T)
    (hdss : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (y' Y : ℕ)
      (cO : ℤ → O), (∀ x : ℤ, ((l : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) →
      ∀ xs : List ℤ, (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
        IsJumpV PD T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) →
      ∀ seq : ℕ → W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp W ^ Y • seq 0 ∈ W.N T →
      (∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
        W.γD T W.gam (seq k) - seq k) →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq xs.length ∈ W.N T) :
    Formalism.MainNotions.N.LetterConditionLocal W := by
  intro hCA T hT i y _ dop hdop cc hcc X hX z hz
  obtain ⟨hDL, hzN⟩ := dl_of_qp W (hR9 hCA T hT) hz
  have hcc' : ∀ x : ℤ, ((l : ℕ) : O) * cc x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have e := hcc x
    rw [hpl] at e
    linear_combination -e
  have hj : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
      IsJumpV PD T.ρ τ a → 0 < j → j ≤ y → a + (j : ℤ) ∈ X.toList :=
    fun τ a j ho hja h1 h2 => Finset.mem_toList.2 (hX τ a j ho hja h1 h2)
  have hrec : ∀ k < X.toList.length, W.π₀ • (pseq W dop cc X.toList z (k + 1) +
      cc (X.toList.getD k 0) • pseq W dop cc X.toList z k) =
      W.γD T W.gam (pseq W dop cc X.toList z k) - pseq W dop cc X.toList z k := by
    intro k hk
    rw [pseq_succ W dop cc X.toList z k hk, sub_add_cancel]
    exact hdop _
  have key := hdss hCA T hT i 0 y cc hcc' X.toList hj (pseq W dop cc X.toList z)
    (by rw [pseq_zero]; exact hDL) (by rw [pseq_zero]; exact hzN) hrec
  rw [pseq_length] at key
  obtain ⟨hD, hNl⟩ := key
  rw [pow_zero, one_smul] at hNl
  refine ⟨⟨hNl, hD.2⟩, Submodule.mem_map.2 ⟨_, hNl, ?_⟩⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact hD.1

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

open Formalism.BasicNotions.Loc

theorem eigenvalue_product_maps_letter_lattice_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  intro D HW F Cm hN l _ K s LL h hCA
  have hs : s = 1 := by rw [← (HW l).W_s K s LL h]; exact hCA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, h⟩
    obtain ⟨w, hw⟩ := hCA.1.2 ⟨x, hx⟩
    have h2 := w.2.2
    have : ((w : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hw
    rw [this] at h2
    exact h2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL h) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL h
  exact eigenvalue_product_maps_letter_lattice_local _ l hpl (fun hA T hT => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.ring_hypotheses_of_crystalline _ hA h9 T hT)
    (fun _ => GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl) hCA

end GlobalTheory.PrimeSequence
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsAStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letterConditionGlobal_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  first | exact @GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | exact GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions | (intros; apply GlobalTheory.PrimeSequence.eigenvalue_product_maps_letter_lattice_of_conclusions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section LetterAux

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem γD_letE_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem sum_letE_eq_one [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem le_Mmax_of [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Formalism.MainNotions.LiftingTheory.Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem smul_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : a • x ∈ W.N T) : a • ((letE i : LetA O n) • x) ∈ W.N T := by
  rw [smul_smul, mul_comm, ← smul_smul]
  exact (W.N T).smul_mem _ hx

theorem letE_rec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (c : O)
    (y z : W.DD T) (h : W.π₀ • (y + c • z) = W.γD T W.gam z - z) :
    W.π₀ • ((letE i : LetA O n) • y + c • ((letE i : LetA O n) • z)) =
      W.γD T W.gam ((letE i : LetA O n) • z) - (letE i : LetA O n) • z := by
  rw [smul_comm c (letE i : LetA O n) z, ← smul_add, smul_smul, mul_comm W.π₀, ← smul_smul, h,
    smul_sub, γD_letE_smul]

theorem mem_N_of_letE [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ i : ZMod n, (letE i : LetA O n) • x ∈ W.N T) : x ∈ W.N T := by
  have e : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one, one_smul]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => h i)

theorem mem_of_qp_pow_zero (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ 0 • x ∈ W.N T) : x ∈ W.N T := by
  rwa [pow_zero, one_smul] at h

end LetterAux

theorem dss_semisimple_of_used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc Y y₀ hy hΔ seq h0 hrec
  subst h0
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hw1 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL h).gam_gen
    rw [hA.2.1, Nat.cast_one] at this
    exact this
  have hug1 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have := hug
    rw [hpl] at this
    exact this
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug1 hv hw1
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - ((((((HW l).W K 1 LL h).χΓ
      ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) := by
    intro x
    have := hc x
    rw [hpl, hug'] at this
    exact this
  have hjx : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL h) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → 0 < j → j ≤ Y →
      a + (j : ℤ) ∈ Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y := by
    intro i τ a j hO hjump hj0 hjY
    have ha := hJ i τ hO a hjump
    have hM := le_Mmax_of Mi i
    have hH := le_Mmax_of hi i
    rw [Formalism.MainNotions.LiftingTheory.xList, Finset.mem_sort, Finset.mem_image]
    refine ⟨(a, (j : ℤ)), Finset.mem_product.2 ⟨?_, ?_⟩, rfl⟩
    · simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, τ, hjump⟩
      · have := ha.1; omega
      · have := ha.2; omega
    · rw [Finset.mem_Icc]; omega
  have hmem : ∀ i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)),
      (letE i : LetA ↥(OL LL) _) • seq (Formalism.MainNotions.LiftingTheory.xList ((HW l).W K 1 LL h) T (Formalism.MainNotions.LiftingTheory.Mmax _ Mi)
        (Formalism.MainNotions.LiftingTheory.Mmax _ hi) Y).length ∈ ((HW l).W K 1 LL h).N T := by
    intro i
    have hDL : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i ((letE i : LetA ↥(OL LL) _) • seq 0) := by
      refine ⟨by rw [smul_smul, letE_mul_self], fun δ hδ => ?_⟩
      rw [γD_letE_smul ((HW l).W K 1 LL h) T δ i (seq 0)]
      have e2 := hΔ δ hδ
      exact congrArg (fun z => (letE i : LetA ↥(OL LL) _) • z) e2
    have hYi : Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL h) ^ Y • ((letE i : LetA ↥(OL LL) _) • seq 0) ∈
        ((HW l).W K 1 LL h).N T := by
      exact smul_letE_mem ((HW l).W K 1 LL h) T i _ (seq 0) hy
    have key := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i 0 Y cO hc' _
      (fun τ a j hO hjump hj hjY => hjx i τ a j hO hjump hj hjY)
      (fun k => (letE i : LetA ↥(OL LL) _) • seq k) hDL hYi
      (fun k hk => letE_rec ((HW l).W K 1 LL h) T i _ _ _ (hrec k hk))
    exact mem_of_qp_pow_zero ((HW l).W K 1 LL h) T _ key.2
  exact mem_N_of_letE ((HW l).W K 1 LL h) T _ hmem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaOperatorSemisimpleOfConclusionsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_operator_semisimple_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  first | exact @GlobalTheory.dss_semisimple_of_used | exact GlobalTheory.dss_semisimple_of_used | (intros; apply GlobalTheory.dss_semisimple_of_used <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.LiftAdmitted

theorem all_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  intro D HW F Cm
  have hN : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, -⟩ := hN
  have hU : HerrComplexNaturality.HerrExtensionUpToUnit D HW F := GlobalTheory.HerrExtUnit.main D HW F
  have h17 : LiftingTheory.adm17 D HW F := Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hU⟩
  have h18 : LiftingTheory.adm18 D HW F := Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hU⟩
  have h19 : LiftingTheory.adm19 D HW F := GlobalTheory.T.gamma_operator_semisimple_of_conclusions D HW F Cm (GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm)
  have h20 : LiftingTheory.adm20 D HW F := GlobalTheory.T.restriction_corestriction_H1f D HW F
  have h21 : LiftingTheory.adm21 D HW F := class_map_naturality_of_herr D HW F (GlobalTheory.HerrFull.herr_part_a_every_record D HW F)
  have h22 : LiftingTheory.adm22 D HW F := fun l _ K LL =>
    (GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL).1
  have h23 := GlobalTheory.jumps_exact_adm D HW F
  have hA : LiftingTheory.admitted D HW F Cm :=
    ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, h17, h18, h19, h20, h21, h22, h23.2⟩
  refine ⟨hA, ?_⟩
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, h17, h18, h19, h20, h21, h22, h23.1⟩

end GlobalTheory.LiftAdmitted
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmittedStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  first | exact @GlobalTheory.LiftAdmitted.all_admitted | exact GlobalTheory.LiftAdmitted.all_admitted | (intros; apply GlobalTheory.LiftAdmitted.all_admitted <;> assumption)
end
end

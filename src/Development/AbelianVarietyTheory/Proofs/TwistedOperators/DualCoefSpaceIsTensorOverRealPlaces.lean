module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.DualIrr

theorem dual_irr : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro D V θ c hθ hc N hN

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (atTau θ V τ g')⁻¹ = atTau θ V τ g := by
    intro τ g hg
    have hu : IsUnit (gramAt D V τ).det := by
      have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [this]
      exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
    have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    set gi := (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ with hgi
    have h2 : gi * g = 1 := by
      rw [hgi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
    have h3 : g * gi = 1 := mul_eq_one_comm.1 h2
    have hgi' : gi ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      show giᴴ * gramAt D V τ * gi = gramAt D V τ
      calc giᴴ * gramAt D V τ * gi = giᴴ * (gᴴ * gramAt D V τ * g) * gi := by rw [h1]
        _ = (g * gi)ᴴ * gramAt D V τ * (g * gi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [h3]; simp
    refine ⟨gi, hgi', ?_⟩
    have e : atTau θ V τ g * atTau θ V τ gi = 1 := by
      rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hgi', h3, GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ]
    rw [eq_inv_of_mul_eq_one_right e, inv_inv]
  set U := N.dualCoannihilator with hUdef
  have hstab : ∀ a ∈ GinfC V, ∀ v ∈ U, c.ρ a v ∈ U := by
    intro a ha
    refine Submonoid.closure_induction (motive := fun a _ => ∀ v ∈ U, c.ρ a v ∈ U) ?_ ?_ ?_
      (Formalism.IndefR.TopMult.ginf_mem_closure hθ ha)
    · rintro x ⟨τ, g, hg, rfl⟩ v hv
      obtain ⟨g', hg', e⟩ := hinv τ g hg
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro f hf
      have := hv _ (hN τ g' hg' f hf)
      rw [e] at this
      simpa [LinearMap.dualMap_apply] using this
    · intro v hv; simpa using hv
    · intro x y _ _ hx hy v hv
      rw [map_mul, Module.End.mul_apply]
      exact hx _ (hy v hv)
  have hU : ∀ u ∈ GinfC V, U.map (c.ρ u) ≤ U := by
    rintro u hu _ ⟨v, hv, rfl⟩
    exact hstab u hu v hv
  have hN' : U.dualAnnihilator = N := Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases GlobalTheory.GenRealSchur.irr_real c hc U hU with h | h
  · right; rw [← hN', h, Submodule.dualAnnihilator_bot]
  · left; rw [← hN', h, Submodule.dualAnnihilator_top]

end GlobalTheory.DualIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.DualIrr.dual_irr | exact GlobalTheory.DualIrr.dual_irr | (intros; apply GlobalTheory.DualIrr.dual_irr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnita
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnita
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coefA_dual_coef_continuousOn :
    ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  intro D V θ c hθ hc τ f v
  letI := c.nW
  letI := c.iW
  haveI := c.fW
  have h1 : Continuous fun h : GA D V => c.ρ h v := hc.2.2.1 v
  have hinv : Continuous (fun h : GA D V => h⁻¹) := continuous_inv
  have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
  exact (hf.comp (h1.comp hinv)).comp_continuousOn (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnitaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  first | exact @GlobalTheory.coefA_dual_coef_continuousOn | exact GlobalTheory.coefA_dual_coef_continuousOn | (intros; apply GlobalTheory.coefA_dual_coef_continuousOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorDecomp

open GlobalTheory.Chain.IoLift Module

section Cyclic

variable {ι : Type} {W : Type} [AddCommGroup W] [Module ℂ W] {G : ι → Type}
  (a : ∀ i, G i → Module.End ℂ W)

def alg (i : ι) : Subalgebra ℂ (Module.End ℂ W) := Algebra.adjoin ℂ (Set.range (a i))

def ev (i : ι) (w : W) : alg a i →ₗ[ℂ] W :=
  LinearMap.applyₗ w ∘ₗ (alg a i).val.toLinearMap

def cyc (i : ι) (w : W) : Submodule ℂ W := LinearMap.range (ev a i w)

variable {a}

theorem mem_cyc {i : ι} {w v : W} : v ∈ cyc a i w ↔ ∃ α ∈ alg a i, α w = v := by
  simp only [cyc, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨α, hα⟩, rfl⟩
    exact ⟨α, hα, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨⟨α, hα⟩, rfl⟩

theorem gen_mem_alg (i : ι) (g : G i) : a i g ∈ alg a i := Algebra.subset_adjoin ⟨g, rfl⟩

theorem self_mem_cyc (i : ι) (w : W) : w ∈ cyc a i w := mem_cyc.2 ⟨1, (alg a i).one_mem, Module.End.one_apply w⟩

theorem apply_mem_cyc {i : ι} {w v : W} (hv : v ∈ cyc a i w) {β : Module.End ℂ W} (hβ : β ∈ alg a i) :
    β v ∈ cyc a i w := by
  obtain ⟨α, hα, rfl⟩ := mem_cyc.1 hv
  exact mem_cyc.2 ⟨β * α, (alg a i).mul_mem hβ hα, rfl⟩

theorem alg_stable {i : ι} (N : Submodule ℂ W) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N)
    {α : Module.End ℂ W} (hα : α ∈ alg a i) : ∀ x ∈ N, α x ∈ N := by
  unfold alg at hα
  induction hα using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hN g
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hx
  | add x y _ _ h1 h2 =>
    intro z hz
    rw [LinearMap.add_apply]
    exact N.add_mem (h1 z hz) (h2 z hz)
  | mul x y _ _ h1 h2 =>
    intro z hz
    rw [Module.End.mul_apply]
    exact h1 _ (h2 z hz)

theorem cyc_le {i : ι} {w : W} (N : Submodule ℂ W) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N) (hw : w ∈ N) :
    cyc a i w ≤ N := by
  intro v hv
  obtain ⟨α, hα, rfl⟩ := mem_cyc.1 hv
  exact alg_stable N hN hα w hw

theorem commute_alg (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {i j : ι} (hij : i ≠ j)
    {α β : Module.End ℂ W} (hα : α ∈ alg a i) (hβ : β ∈ alg a j) : Commute α β := by
  unfold alg at hα hβ
  induction hβ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    induction hα using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact hc i j hij g h
    | algebraMap r => exact Algebra.commute_algebraMap_left r _
    | add y z _ _ h1 h2 => exact h1.add_left h2
    | mul y z _ _ h1 h2 => exact h1.mul_left h2
  | algebraMap r => exact Algebra.commute_algebraMap_right r _
  | add y z _ _ h1 h2 => exact h1.add_right h2
  | mul y z _ _ h1 h2 => exact h1.mul_right h2

theorem cyc_apply_le (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {i j : ι} (hij : i ≠ j)
    {α : Module.End ℂ W} (hα : α ∈ alg a i) (w : W) : cyc a j (α w) ≤ (cyc a j w).map α := by
  intro v hv
  obtain ⟨β, hβ, rfl⟩ := mem_cyc.1 hv
  rw [Submodule.mem_map]
  refine ⟨β w, mem_cyc.2 ⟨β, hβ, rfl⟩, ?_⟩
  exact LinearMap.congr_fun (commute_alg hc hij hα hβ).eq w

theorem eq_cyc_of_min [Fintype ι] [FiniteDimensional ℂ W]
    (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) {w₀ : W}
    (hmin : ∀ w : W, w ≠ 0 → ∑ i, finrank ℂ (cyc a i w₀) ≤ ∑ i, finrank ℂ (cyc a i w))
    (i : ι) (N : Submodule ℂ W) (hle : N ≤ cyc a i w₀) (hN : ∀ g, ∀ x ∈ N, a i g x ∈ N) (hne : N ≠ ⊥) :
    N = cyc a i w₀ := by
  classical
  obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨α, hα, hαw⟩ := mem_cyc.1 (hle hwN)
  have h1 : cyc a i w ≤ N := cyc_le N hN hwN
  have hle' : ∀ j ∈ (Finset.univ : Finset ι), finrank ℂ (cyc a j w) ≤ finrank ℂ (cyc a j w₀) := by
    intro j _
    by_cases hij : i = j
    · subst hij
      exact Submodule.finrank_mono (h1.trans hle)
    · rw [← hαw]
      exact (Submodule.finrank_mono (cyc_apply_le hc hij hα w₀)).trans (Submodule.finrank_map_le _ _)
  have heq := (Finset.sum_eq_sum_iff_of_le hle').1 (le_antisymm (Finset.sum_le_sum hle') (hmin w hw0))
  have hi := Submodule.eq_of_le_of_finrank_eq (h1.trans hle) (heq i (Finset.mem_univ i))
  exact le_antisymm hle (hi ▸ h1)

theorem absIrr_of_irr {K : Type} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K] [Nontrivial K]
    {H : Type} (b : H → Module.End ℂ K)
    (hb : ∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, b g x ∈ N) → N = ⊥ ∨ N = ⊤) : AbsIrr b := by
  refine ⟨hb, fun T hT => ?_⟩
  obtain ⟨c, hcT⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have hstab : ∀ g, ∀ x ∈ LinearMap.ker (T - c • LinearMap.id), b g x ∈ LinearMap.ker (T - c • LinearMap.id) := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := LinearMap.congr_fun (hT g) x
    have h2 := congrArg (b g) hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, map_smul, map_zero] at hx h h2 ⊢
    rw [h]
    exact h2
  rcases hb _ hstab with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hcT.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    apply hv0
    have hmem : v ∈ LinearMap.ker (T - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hv.apply_eq_smul, sub_self]
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · ext x
    have hx : x ∈ LinearMap.ker (T - c • LinearMap.id) := by
      rw [h]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx

end Cyclic

section Prod

variable {ι : Type} [Fintype ι] {W : Type} [AddCommGroup W] [Module ℂ W] {G : ι → Type}
  {a : ∀ i, G i → Module.End ℂ W} (hc : ∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g)
  {w₀ : W} (s : ∀ i, cyc a i w₀ →ₗ[ℂ] alg a i)

def prodAt (x : ∀ i, cyc a i w₀) (S : Finset ι) : Module.End ℂ W :=
  S.noncommProd (fun i => (s i (x i) : Module.End ℂ W))
    (fun i _ j _ hij => commute_alg hc hij (s i (x i)).2 (s j (x j)).2)

theorem prodAt_univ_eq [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) :
    prodAt hc s x Finset.univ = prodAt hc s x (Finset.univ.erase i) * (s i (x i) : Module.End ℂ W) := by
  unfold prodAt
  exact (Finset.noncommProd_erase_mul _ (Finset.mem_univ i) _ _).symm

theorem prodAt_erase_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (v : cyc a i w₀) :
    prodAt hc s (Function.update x i v) (Finset.univ.erase i) = prodAt hc s x (Finset.univ.erase i) := by
  unfold prodAt
  apply Finset.noncommProd_congr rfl
  intro j hj
  show ((s j (Function.update x i v j) : alg a j) : Module.End ℂ W) = s j (x j)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem prodAt_erase_commute [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) {α : Module.End ℂ W}
    (hα : α ∈ alg a i) : Commute α (prodAt hc s x (Finset.univ.erase i)) := by
  unfold prodAt
  apply Finset.noncommProd_commute
  intro j hj
  exact commute_alg hc (Finset.ne_of_mem_erase hj).symm hα (s j (x j)).2

variable (hs : ∀ i y, (s i y : Module.End ℂ W) w₀ = y)
include hs

theorem prodAt_univ_apply [DecidableEq ι] (x : ∀ i, cyc a i w₀) (i : ι) :
    prodAt hc s x Finset.univ w₀ = prodAt hc s x (Finset.univ.erase i) (x i : W) := by
  rw [prodAt_univ_eq hc s x i, Module.End.mul_apply, hs]

theorem prodAt_univ_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (v : cyc a i w₀) :
    prodAt hc s (Function.update x i v) Finset.univ w₀ = prodAt hc s x (Finset.univ.erase i) (v : W) := by
  rw [prodAt_univ_apply hc s hs (Function.update x i v) i, prodAt_erase_update hc s, Function.update_self]

omit hs in
theorem prodAt_empty (x : ∀ i, cyc a i w₀) : prodAt hc s x ∅ = 1 := by
  unfold prodAt
  exact Finset.noncommProd_empty _ _

omit hs in
theorem prodAt_insert [DecidableEq ι] (x : ∀ i, cyc a i w₀) {j : ι} {S : Finset ι} (hj : j ∉ S) :
    prodAt hc s x (insert j S) = (s j (x j) : Module.End ℂ W) * prodAt hc s x S := by
  unfold prodAt
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hj

theorem prodAt_base (S : Finset ι) :
    prodAt hc s (fun i => ⟨w₀, self_mem_cyc i w₀⟩) S w₀ = w₀ := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [prodAt_empty hc s, Module.End.one_apply]
  · intro j S hj ih
    rw [prodAt_insert hc s _ hj, Module.End.mul_apply, ih, hs]


omit hs in
def res (a : ∀ i, G i → Module.End ℂ W) (i : ι) (w₀ : W) (g : G i) : Module.End ℂ (cyc a i w₀) :=
  (a i g).restrict (fun _ hx => apply_mem_cyc hx (gen_mem_alg i g))

omit hs in
theorem res_apply (i : ι) (g : G i) (y : cyc a i w₀) : ((res a i w₀ g y : cyc a i w₀) : W) = a i g y := rfl

def mu : (∀ i, cyc a i w₀) →ₘₗ[ℂ] W where
  toFun x := prodAt hc s x Finset.univ w₀
  map_update_add' x i u v := by
    rw [prodAt_univ_update hc s hs, prodAt_univ_update hc s hs, prodAt_univ_update hc s hs,
      Submodule.coe_add, map_add]
  map_update_smul' x i c u := by
    rw [prodAt_univ_update hc s hs, prodAt_univ_update hc s hs, Submodule.coe_smul,
      RingHom.id_apply, map_smul]

theorem mu_apply (x : ∀ i, cyc a i w₀) : mu hc s hs x = prodAt hc s x Finset.univ w₀ := rfl

theorem mu_update {dec : DecidableEq ι} (x : ∀ i, cyc a i w₀) (i : ι) (g : G i) :
    mu hc s hs (Function.update x i (res a i w₀ g (x i))) = a i g (mu hc s hs x) := by
  rw [mu_apply, mu_apply, prodAt_univ_update hc s hs, res_apply, prodAt_univ_apply hc s hs x i]
  exact (LinearMap.congr_fun (prodAt_erase_commute hc s x i (gen_mem_alg i g)).eq (x i : W)).symm

end Prod

theorem tensor_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  intro ι _ _ W _ _ _ _ G a hc hirr
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : W)
  have hex : ∃ n, ∃ w : W, w ≠ 0 ∧ ∑ i, finrank ℂ (cyc a i w) = n := ⟨_, v₀, hv₀, rfl⟩
  obtain ⟨w₀, hw₀, hw₀n⟩ := Nat.find_spec hex
  have hmin : ∀ w : W, w ≠ 0 → ∑ i, finrank ℂ (cyc a i w₀) ≤ ∑ i, finrank ℂ (cyc a i w) := by
    intro w hw
    rw [hw₀n]
    exact Nat.find_min' hex ⟨w, hw, rfl⟩
  have hsec : ∀ i, ∃ t : cyc a i w₀ →ₗ[ℂ] alg a i, (ev a i w₀).rangeRestrict ∘ₗ t = LinearMap.id :=
    fun i => (ev a i w₀).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  choose s hs0 using hsec
  have hs : ∀ i y, (s i y : Module.End ℂ W) w₀ = y := by
    intro i y
    exact congrArg Subtype.val (LinearMap.congr_fun (hs0 i) y)
  have hirr_i : ∀ i, ∀ N : Submodule ℂ (cyc a i w₀), (∀ g, ∀ x ∈ N, res a i w₀ g x ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro i N hN
    by_cases hN0 : N = ⊥
    · exact Or.inl hN0
    right
    have hmap : N.map (cyc a i w₀).subtype = cyc a i w₀ := by
      refine eq_cyc_of_min hc hmin i _ (Submodule.map_subtype_le _ _) ?_ ?_
      · rintro g _ ⟨y, hy, rfl⟩
        exact ⟨res a i w₀ g y, hN g y hy, rfl⟩
      · intro h
        exact hN0 (Submodule.map_injective_of_injective (cyc a i w₀).injective_subtype
          (h.trans (Submodule.map_bot _).symm))
    apply Submodule.map_injective_of_injective (cyc a i w₀).injective_subtype
    rw [hmap, Submodule.map_subtype_top]
  have habs : ∀ i, AbsIrr (res a i w₀) := by
    intro i
    haveI : Nontrivial (cyc a i w₀) :=
      ⟨⟨⟨w₀, self_mem_cyc i w₀⟩, 0, fun h => hw₀ (congrArg Subtype.val h)⟩⟩
    exact absIrr_of_irr _ (hirr_i i)
  obtain ⟨e0, he0⟩ : ∃ e0 : (⨂[ℂ] i, cyc a i w₀) →ₗ[ℂ] W,
      ∀ x, e0 (PiTensorProduct.tprod ℂ x) = mu hc s hs x :=
    ⟨PiTensorProduct.lift (mu hc s hs), fun x => PiTensorProduct.lift.tprod x⟩
  have hint : ∀ i g, e0 ∘ₗ intersection_update_fsHerm_neg_one i (res a i w₀ g) = a i g ∘ₗ e0 := by
    intro i g
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, he0]
    exact mu_update hc s hs x i g
  have hbase : e0 (PiTensorProduct.tprod ℂ (fun i => (⟨w₀, self_mem_cyc i w₀⟩ : cyc a i w₀))) = w₀ := by
    rw [he0, mu_apply]
    exact prodAt_base hc s hs Finset.univ
  have hsurj : LinearMap.range e0 = ⊤ := by
    have hstab : ∀ i g, ∀ x ∈ LinearMap.range e0, a i g x ∈ LinearMap.range e0 := by
      rintro i g _ ⟨t, rfl⟩
      have h := LinearMap.congr_fun (hint i g) t
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      exact LinearMap.mem_range.2 ⟨_, h⟩
    rcases hirr _ hstab with h | h
    · exfalso
      apply hw₀
      have hm : w₀ ∈ LinearMap.range e0 := ⟨_, hbase⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · exact h
  have hker : LinearMap.ker e0 = ⊥ := by
    by_contra hne
    have hstab : ∀ i g, ∀ x ∈ LinearMap.ker e0, intersection_update_fsHerm_neg_one i (res a i w₀ g) x ∈ LinearMap.ker e0 := by
      intro i g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have h := LinearMap.congr_fun (hint i g) x
      simp only [LinearMap.comp_apply] at h
      rw [h, hx, map_zero]
    have htop := GlobalTheory.TensorIrr.eq_top_of_stable ι (fun i => cyc a i w₀) G (fun i => res a i w₀) habs
      (LinearMap.ker e0) hstab hne
    apply hw₀
    rw [← hbase]
    have hm : PiTensorProduct.tprod ℂ (fun i => (⟨w₀, self_mem_cyc i w₀⟩ : cyc a i w₀)) ∈ LinearMap.ker e0 := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.1 hm
  let e := LinearEquiv.ofBijective e0 ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hsurj⟩
  refine ⟨fun i => cyc a i w₀, fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
    fun i => res a i w₀, fun i => (cyc a i w₀).subtype, e, fun i => (cyc a i w₀).injective_subtype,
    fun i g x => rfl, hirr_i, ?_⟩
  intro i g x
  show e0 _ = a i g (e0 _)
  rw [he0, he0]
  exact mu_update hc s hs x i g

end GlobalTheory.TensorDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamiliesStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorDecomposition_commutingFamilies : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ W), (∀ i j, i ≠ j → ∀ g h, a i g * a j h = a j h * a i g) → (∀ N : Submodule ℂ W, (∀ i g, ∀ x ∈ N, a i g x ∈ N) → N = ⊥ ∨ N = ⊤) → ∃ (X : ι → Type) (_ : ∀ i, AddCommGroup (X i)) (_ : ∀ i, Module ℂ (X i)) (_ : ∀ i, FiniteDimensional ℂ (X i)) (b : ∀ i, G i → Module.End ℂ (X i)) (m : ∀ i, X i →ₗ[ℂ] W) (e : (⨂[ℂ] i, X i) ≃ₗ[ℂ] W), (∀ i, Function.Injective (m i)) ∧ (∀ i g x, m i (b i g x) = a i g (m i x)) ∧ (∀ i, ∀ N : Submodule ℂ (X i), (∀ g, ∀ x ∈ N, b i g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧ ∀ i g (x : ∀ i, X i), e (PiTensorProduct.tprod ℂ (Function.update x i (b i g (x i)))) = a i g (e (PiTensorProduct.tprod ℂ x)) := by
  first | exact @GlobalTheory.TensorDecomp.tensor_decomp | exact GlobalTheory.TensorDecomp.tensor_decomp | (intros; apply GlobalTheory.TensorDecomp.tensor_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualCoefSpaceIsTensorOverRealPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefTensorProof

theorem coefTensor : CoefTensor := by
  intro D V θ c hθ hc
  classical
  haveI : Nontrivial c.W := hc.2.2.2.1
  haveI : Nontrivial (Module.Dual ℂ c.W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  let a : ∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.UH (gramAt D V τ) → Module.End ℂ (Module.Dual ℂ c.W) :=
    fun τ g => (c.ρ (atTau θ V τ g.1)⁻¹).dualMap
  have ha : ∀ τ (g : Formalism.QuantumDeterminants.UH (gramAt D V τ)) f, a τ g f = f ∘ₗ c.ρ (atTau θ V τ g.1)⁻¹ := fun _ _ _ => rfl
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g h, a τ g * a τ' h = a τ' h * a τ g := by
    intro τ τ' hne g h
    have hc' := GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne g.1 g.2 h.1 h.2
    ext f w
    simp only [Module.End.mul_apply, ha, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (c.ρ _), ← map_mul, ← Module.End.mul_apply (c.ρ _), ← map_mul, ← mul_inv_rev,
      ← mul_inv_rev, hc']
  have hirrD : ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ g, ∀ x ∈ N, a τ g x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces D V θ c hθ hc N fun τ g hg f hf => hN τ ⟨g, hg⟩ f hf
  obtain ⟨X, i1, i2, i3, b, m, e, hinj, hint, hirr, heq⟩ := GlobalTheory.T.exists_tensorDecomposition_commutingFamilies D.what₂.Tau (Module.Dual ℂ c.W) _ a hcomm hirrD
  have hone : ∀ τ, atTau θ V τ 1 = 1 := fun τ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  let π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (X τ) := fun τ g =>
    if hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then b τ ⟨g, hg⟩ else 1
  have hπ : ∀ τ g (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), π τ g = b τ ⟨g, hg⟩ := fun τ g hg => dif_pos hg
  refine ⟨X, i1, i2, i3, π, e, fun τ => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    rw [hπ τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)]
    ext x
    apply hinj τ
    rw [hint, ha]
    show m τ x ∘ₗ c.ρ (atTau θ V τ 1)⁻¹ = m τ x
    rw [hone, inv_one, map_one]
    rfl
  · intro g hg h hh
    rw [hπ τ _ (GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh), hπ τ g hg, hπ τ h hh]
    ext x
    apply hinj τ
    rw [Module.End.mul_apply, hint, hint, hint]
    ext w
    simp only [ha, LinearMap.comp_apply]
    rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hh, mul_inv_rev, map_mul, Module.End.mul_apply]
  · intro w l
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (m τ) (LinearMap.ker_eq_bot.2 (hinj τ))
    obtain ⟨v, hv⟩ : ∃ v : c.W, ∀ φ : Module.Dual ℂ c.W, (l ∘ₗ r) φ = φ v :=
      ⟨(Module.evalEquiv ℂ c.W).symm (l ∘ₗ r), fun φ => by
        conv_lhs => rw [← (Module.evalEquiv ℂ c.W).apply_symm_apply (l ∘ₗ r)]
        rfl⟩
    refine (GlobalTheory.T.contragredient_matrix_coefficient_continuousOn_unitary D V θ c hθ hc τ (m τ w) v).congr fun g hg => ?_
    show l (π τ g w) = _
    rw [hπ τ g hg]
    have : l (b τ ⟨g, hg⟩ w) = (l ∘ₗ r) (m τ (b τ ⟨g, hg⟩ w)) := by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply r, hr, LinearMap.id_apply]
    rw [this, hv, hint, ha, LinearMap.comp_apply]
  · intro U hU
    exact hirr τ U fun g x hx => by rw [← hπ τ g.1 g.2]; exact hU g.1 g.2 x hx
  · intro τ g hg x y hy hy'
    have : y = Function.update x τ (b τ ⟨g, hg⟩ (x τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h; rw [Function.update_self, hy, hπ _ g hg]
      · rw [Function.update_of_ne h, hy' τ' h]
    rw [this, heq]
    rfl

end GlobalTheory.CoefTensorProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualCoefSpaceIsTensorOverRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces : CoefTensor := by
  first | exact @GlobalTheory.CoefTensorProof.coefTensor | exact GlobalTheory.CoefTensorProof.coefTensor | (intros; apply GlobalTheory.CoefTensorProof.coefTensor <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Formalism.LocalToGlobal.Columns.LocWLemmas

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ProjDescent

section SlopeTestRemainingChoices

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction (h : SemiBC u) (P : N → Prop) (h0 : ∀ x, P (u x)) (h1 : ∀ y z, P y → P z → P (y + z))
    (h2 : ∀ (b : B) y, P y → P (b • y)) (y : N) : P y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

end SlopeTestRemainingChoices

theorem descent : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  intro A B D _ _ _ f p q hpq hf hfix P _ _ _ _ PB _ _ PD _ _ u u₁ u₂ w hu hw h₁ h₂
  classical
  obtain ⟨n, s, g, -, -, hsg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hx : ∀ x, s (g x) = x := fun x => LinearMap.congr_fun hsg x
  set e : Fin n → P := fun i => s (fun j => if i = j then 1 else 0) with he
  have hdec : ∀ c : Fin n → A, u (s c) = ∑ i, f (c i) • u (e i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.pi_apply_eq_sum_univ s c, map_sum]
    simp only [LinearMap.map_smulₛₗ, e]
  obtain ⟨WB, hWB, -⟩ := hu (Fin n → B)
    { toFun := fun x i => f (g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  obtain ⟨WD, hWD, -⟩ := hw (Fin n → D)
    { toFun := fun x i => p (f (g x i))
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  have hWB' : ∀ x i, WB (u x) i = f (g x i) := fun x i => congrFun (hWB x) i
  have hWD' : ∀ x i, WD (w x) i = p (f (g x i)) := fun x i => congrFun (hWD x) i
  have hrec : ∀ z, z = ∑ i, WB z i • u (e i) := by
    intro z
    refine induction hu (fun z => z = ∑ i, WB z i • u (e i)) (fun x => ?_) (fun y z hy hz => ?_)
      (fun b y hy => ?_) z
    · conv_lhs => rw [← hx x]
      rw [hdec]; simp only [hWB']
    · conv_lhs => rw [hy, hz]
      simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · conv_lhs => rw [hy]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hp : ∀ z i, p (WB z i) = WD (u₁ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, p (WB z i) = WD (u₁ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₁, hWD', hWB']
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  have hq : ∀ z i, q (WB z i) = WD (u₂ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, q (WB z i) = WD (u₂ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₂, hWD', hWB']
      exact (RingHom.congr_fun hpq (g x i)).symm
    · simp only [map_add (f := _), Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  refine ⟨fun x y hxy => ?_, fun z hz => ?_⟩
  · have hg : g x = g y := funext fun i => hf (by rw [← hWB', ← hWB', hxy])
    rw [← hx x, ← hx y, hg]
  · have hb : ∀ i, ∃ b, f b = WB z i := fun i => RingHom.mem_range.1 (hfix _ (by rw [hp, hq, hz]))
    choose b hb using hb
    exact ⟨s b, by rw [hdec]; simp only [hb]; exact (hrec z).symm⟩

end GlobalTheory.BSP.ProjDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projective_module_element_descent_equalizer : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  first | exact @GlobalTheory.BSP.ProjDescent.descent | exact GlobalTheory.BSP.ProjDescent.descent | (intros; apply GlobalTheory.BSP.ProjDescent.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapTensorOneCommDiagonalAction
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section PotTransport

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem linearMap_tensorOne_comm_diagonalAction {H : Type} [Group H] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Algebra Qp K₁] [Algebra Qp K₂] [Algebra K₁ K₂] [IsScalarTower Qp K₁ K₂]
    [Algebra K₁ B] [IsScalarTower Qp K₁ B]
    [Algebra K₁ BdR] [Algebra K₂ BdR] [IsScalarTower Qp K₂ BdR]
    [IsScalarTower K₁ K₂ BdR] [IsScalarTower Qp K₁ BdR]
    (PD : PeriodData H Qp K₁ K₂ B BdR) {σ : Representation LL H V} {σ' : Representation LL H V'}
    (f : V →ₗ[LL] V') (hf : ∀ g v, f (σ g v) = σ' g (f v)) (g : H) (x : V ⊗[Qp] B) :
    SumJumps.ext1 Qp B f (actVB PD σ g x) = actVB PD σ' g (SumJumps.ext1 Qp B f x) := by
  unfold actVB
  rw [SumJumps.ext1_comm f (σ g) (σ' g) (hf g)]

theorem eq_map_of_equiv_tensor (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] B)) (S' : Submodule LL (V' ⊗[Qp] B))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp B e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp B e.symm.toLinearMap x ∈ S) :
    S = S'.map (SumJumps.ext1 Qp B e.symm.toLinearMap) := by
  apply le_antisymm
  · intro x hx
    refine ⟨_, a x hx, ?_⟩
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  · rintro _ ⟨y, hy, rfl⟩
    exact b y hy

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dpcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ PC.Dpcris ρ, SumJumps.ext1 Qp B f x ∈ PC.Dpcris ρ' :=
  SumJumps.dcris_map PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') f (fun h v => hf (h : G) v)

theorem eig_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (I : Subgroup G)
    (a : I →* LLˣ) : ∀ x ∈ PC.Eig ρ I a, SumJumps.ext1 Qp B f x ∈ PC.Eig ρ' I a := by
  intro x hx
  simp only [PotCrysData.Eig, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨dpcris_map PC f hf x hx.1, fun g => ?_⟩
  rw [← linearMap_tensorOne_comm_diagonalAction PC.PD f hf, hx.2 g, map_smul]

theorem potCrys_inertiaThrough_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧
      ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S := by
  have he' : ∀ g v, e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) :=
    symm_equivariant e he
  refine ⟨fun h => isCrys_of_equiv PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') e (fun h v => he (h : G) v) h, fun S hS => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨h1, h2, ?_⟩
  have hD : PC.Dpcris ρ = (PC.Dpcris ρ').map (SumJumps.ext1 Qp B e.symm.toLinearMap) :=
    eq_map_of_equiv_tensor e _ _ (dpcris_map PC e.toLinearMap he)
      (dpcris_map PC e.symm.toLinearMap he')
  have hE : ∀ a, PC.Eig ρ PC.Iner a =
      (PC.Eig ρ' PC.Iner a).map (SumJumps.ext1 Qp B e.symm.toLinearMap) := fun a =>
    eq_map_of_equiv_tensor e _ _ (eig_map PC e.toLinearMap he _ a)
      (eig_map PC e.symm.toLinearMap he' _ a)
  rw [hD, h3, Submodule.map_iSup]
  congr 1; ext a
  rw [Submodule.map_iSup, hE]

end PotTransport

end GlobalTheory.HTW.Rec

theorem GlobalTheory.HTW.Rec.potCrysData_transport : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (e : V ≃ₗ[LL] V'),
    (∀ g v, e (ρ g v) = ρ' g (e v)) →
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧ ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S :=
  by
  intros
  exact GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ ‹_› ‹_›
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesConjOfAdm
noncomputable section

namespace GlobalTheory.GoodTypes

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant
open scoped Classical

section Local

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {G V U : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U]

def ConjIn (ρ : Representation ℂ G V) (W : Submodule ℂ V) (j : Gn g n →* G)
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) U) : Prop :=
  ∀ y ∈ W, y ≠ 0 → ∃ Λ : V →ₛₗ[starRingEnd ℂ] U, Λ y ≠ 0 ∧
    ∀ z ∈ W, Λ z ∈ fixK1 π ∧ ∀ h, Λ (ρ (j h) z) = π (lift g n h) (Λ z)

theorem ConjIn.act_ne {ρ : Representation ℂ G V} {W : Submodule ℂ V} {j : Gn g n →* G}
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) U} (h : ConjIn ρ W j π) (a a' : MonoidAlgebra ℂ (Gn g n))
    (ha : ∀ x, starRingEnd ℂ (a.coeff x) = a'.coeff x) {y : V} (hy : y ∈ W) (h0 : y ≠ 0)
    (hfix : ∑ x, a.coeff x • ρ (j x) y = y) : ∃ u ∈ fixK1 π, actK π a' u ≠ 0 := by
  obtain ⟨Λ, h1, h2⟩ := h y hy h0
  refine ⟨Λ y, (h2 y hy).1, ?_⟩
  have : actK π a' (Λ y) = Λ y := by
    conv_rhs => rw [← hfix]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, actK, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.smul_apply, map_smulₛₗ, ha, (h2 y hy).2]
  rwa [this]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (h : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod) : f = f' := by
  have h3 := congrArg Polynomial.roots h
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g), ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) (Multiset.map_injective hτ h3)

end Local

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroPrime (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def facHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Gn (D.host.g k) D.R.r →* G0g D.nd :=
  MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩

abbrev LocRep (D : D7) (k : Fin 2) : Type 1 := Rep.{0} ℂ (GL (Fin D.R.r) ℚ_[D.host.g k])

abbrev Comp (D : D7) : Type 1 := D.what₂.FT → ∀ k : Fin 2, D.nd.PlG k → LocRep D k

def SeriesConj (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f →
    (D.ntypes.eSer k f).coeff.mapRange (starRingAut : ℂ ≃+* ℂ) (map_zero _) =
      (D.ntypes.eSer k (labAct D starRingAut k f)).coeff

theorem labAct_conj (D : D7) (k : Fin 2) {f : (ZMod (D.host.g k))[X]} (hf : IsLabel D k f) :
    labAct D starRingAut k f = dualLab D k f := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Compare.TeichmullerRoots.dual_spec hf.1 hf.2.2
  refine GlobalTheory.Compare.TeichmullerRoots.labAct_eq D k _ (-1) (fun ζ hζ => ?_) hf h1 h2
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ
    (GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport.rootExp_ne_zero D.R.r _ (D.host.g_prime k).two_le)
  rw [zpow_neg_one, Complex.inv_eq_conj hn]
  rfl

theorem act_atPlace (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V)
    (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)) (y : V) :
    ρ.asAlgebraHom (atPlace D k v a) y = ∑ x, a.coeff x • ρ (facHom D k v x) y := by
  rw [GlobalTheory.SeriesSupportTest.atPlace_eq]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    have : GlobalTheory.SeriesSupportTest.plHom D k v (MonoidAlgebra.single h c) =
        MonoidAlgebra.single (facHom D k v h) c := MonoidAlgebra.mapDomain_single
    rw [this, Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem exists_good (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) {x : V}
    (hx : x ≠ 0) (he : ρ.asAlgebraHom D.ntypes.e0 x = x) :
    ∃ (t : Tup2 D) (a : MonoidAlgebra ℂ (G0g D.nd)), D.ntypes.goodTuple t ∧ ρ.asAlgebraHom a x ≠ 0 ∧
      ∀ k v, ρ.asAlgebraHom (atPlace D k v (D.ntypes.eSer k (t k v))) (ρ.asAlgebraHom a x) = ρ.asAlgebraHom a x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Ten.e0_eq, Ten.eGood, map_sum, LinearMap.sum_apply] at he
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (he.trans_ne hx)
  by_cases hg : Ten.goodVec D p
  · rw [if_pos hg] at hp
    refine ⟨_, _, hg, hp, fun k v => ?_⟩
    rw [← Module.End.mul_apply, ← map_mul,
      ← Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D k v _ (D.ntypes.eSer_central k _)),
      Ten.atPlace_eq, Ten.tens_mul_plc]
    congr 3
    exact Function.update_eq_self_iff.2 (D.ntypes.eSer_idem _ _)
  · rw [if_neg hg] at hp
    simp at hp

variable {D : D7} {X : BaseLevelRowSide D}

end GlobalTheory.GoodTypes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorialMulEqPowAinf
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_factorial_mul_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) l hp.ne_one
  have hk : k ≤ n := by
    have h1 : k ≤ padicValNat l n.factorial :=
      ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    have h2 : (l - 1) * padicValNat l n.factorial = n - (l.digits n).sum := by
      simpa only [Nat.padicValNat_def] using hp.sub_one_mul_multiplicity_factorial (n := n)
    have h3 : 1 ≤ l - 1 := by have := hp.two_le; omega
    have h4 : padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hu : IsUnit ((m : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨u * (l : ℤ_[l]) ^ j, ?_⟩
  rw [h]
  push_cast
  linear_combination ((l : ℤ_[l]) ^ (k + j)) * hu

theorem exists_factorial_mul_eq_pow_ainf (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : Ainf l, ((n.factorial : ℕ) : Ainf l) * c = ((l : ℕ) : Ainf l) ^ n := by
  obtain ⟨c, hc⟩ := exists_factorial_mul_eq_pow l n
  refine ⟨algebraMap ℤ_[l] (Ainf l) c, ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using congrArg (algebraMap ℤ_[l] (Ainf l)) hc

end GlobalTheory.Per
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.AcrisPow
variable {l : ℕ} [hl : Fact l.Prime]

theorem eventually_lt_two_pow (A B : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → A * n + B < 2 ^ n := by
  refine ⟨4 * (A + B + 1), fun n hn => ?_⟩
  set m := 2 * (A + B + 1) with hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m ≤ n by omega)
  have hk : m ≤ k := by omega
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 h2
  rw [pow_add]
  have h4 : A * (m + k) + B < (m + 1) * (k + 1) := by nlinarith
  omega

theorem dvd_pow_acris0 (ξ : Ainf l) (hξ : Per.θ l ξ = 0) :
    ((l : ℕ) : Per.Acris0 l) ∣ algebraMap (Ainf l) (Per.Acris0 l) ξ ^ l := by
  have hp : l.Prime := Fact.out
  have hlu : IsUnit ((l : ℕ) : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)
    rwa [map_natCast] at this
  have hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l) := by
    obtain ⟨c, hc⟩ := GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc
    rw [map_mul, map_pow, map_natCast, map_natCast] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l := by rw [← mul_assoc, hv, one_mul]
  generalize v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx
  have hxD : x ∈ Per.Acris0 l := GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx
  have hfac : ((l.factorial : ℕ) : Per.AinfP l) =
      ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  refine ⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]
  rw [← hx, hfac, mul_assoc]

theorem dvd_X_pow {K : FinExt l} (bk : BK K) :
    (l : Per.Acris l) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (bk.Ep.natDegree * l) := by
  set f := algebraMap (Ainf l) (Per.Acris l)
  have hξ : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l := by
    have := map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)
    rw [map_natCast, map_pow, ← GlobalTheory.RingIface.tower l] at this
    exact this
  have h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree := by
    have := map_dvd f (AinfDiv.dvd_E bk)
    rwa [map_natCast, map_sub, map_pow] at this
  have h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l :=
    h2.trans (sub_dvd_pow_sub_pow _ _ l)
  have h4 := dvd_sub h1 h3
  rw [sub_sub_cancel, ← pow_mul] at h4
  simpa [RingHom.comp_apply] using h4

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  intro l _ K bk c M
  set e := bk.Ep.natDegree
  obtain ⟨n₀, hn₀⟩ := eventually_lt_two_pow (e * l * c) (e * l * M)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2l : 2 ^ n ≤ l ^ n := Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n
  have hle : e * l * (c * n + M) ≤ l ^ n - 1 := by
    have : e * l * (c * n + M) = e * l * c * n + e * l * M := by ring
    omega
  have hk := pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)
  rw [← pow_mul] at hk
  exact hk.trans (pow_dvd_pow _ hle)

end GlobalTheory.AcrisPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventuallyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  first | exact @GlobalTheory.AcrisPow.main | exact GlobalTheory.AcrisPow.main | (intros; apply GlobalTheory.AcrisPow.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamily
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AdaptedHodge

variable {l : ℕ} [Fact l.Prime]

theorem xi_unit_fil (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ u : (Per.BdR l)ˣ, (u : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ∧
      ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a →
        ∃ w : Per.BdRp l, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  have he := core_isEps l C
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have h1 : xi C.ε ∈ Ideal.span {ξ} := by rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  have h2 : ξ ∈ Ideal.span {xi C.ε} := by rw [← C.ker_theta, ← hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨b0, hb0⟩ := Ideal.mem_span_singleton'.1 h2
  have hX := TiedUnif.isUnit_xi he
  have key : aDp l a0 * aDp l b0 * aDp l (xi C.ε) = aDp l (xi C.ε) := by
    rw [← map_mul, ← map_mul, mul_assoc, hb0, ha0]
  have hab : aDp l a0 * aDp l b0 = 1 := by
    apply hinj
    rw [map_one]
    apply hX.mul_right_cancel
    rw [one_mul, ← map_mul, key]
  have hα : IsUnit (aDp l a0) := IsUnit.of_mul_eq_one _ hab
  have hXe : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi C.ε)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a0) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) := by
    rw [← map_mul, ← map_mul, ha0]
  have hu : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ)) :=
    isUnit_of_mul_isUnit_right (hXe ▸ hX)
  refine ⟨hu.unit, hu.unit_spec, fun a x hx => ?_⟩
  obtain ⟨w, rfl⟩ := (TiedUnif.mem_FilD_iff he a x).1 hx
  have hEq : hX.unit = hu.unit * Units.map (algebraMap (Per.BdRp l) (Per.BdR l) : Per.BdRp l →* Per.BdR l) hα.unit :=
    Units.ext (by simp [hXe, mul_comm])
  refine ⟨((hα.unit ^ a : (Per.BdRp l)ˣ) : Per.BdRp l) * w, ?_⟩
  rw [hEq, mul_zpow, ← map_zpow, Units.val_mul, map_mul, mul_assoc]
  rfl

end GlobalTheory.BKLim.AdaptedHodge

namespace GlobalTheory.BKLim

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  intro l _ K P AI T C hfit ξ hξ d ρ x h hinv hfil hspan
  obtain ⟨u, hu, hF⟩ := AdaptedHodge.xi_unit_fil C ξ hξ
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have hV : ∀ j i, ∃ w : Per.BdRp l, T.eD (x j i) = ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w :=
    fun j i => hF _ _ ((T.fil K _ _).1 (hfil j i))
  choose w hw using hV
  have h0 : ∀ i (k : Fin d), (Pi.single i (1 : P.R.BdR) : Fin d → P.R.BdR) k ∈ (P.PD K).Fil 0 := by
    intro i k
    rw [T.fil]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))]
      exact TiedUnif.alg_mem_FilD_zero 1
    · rw [Pi.single_eq_of_ne hk, map_zero]
      exact zero_mem _
  choose c hc hsum using fun i => hspan (Pi.single i 1) (h0 i)
  have hW : ∀ i j, ∃ w' : Per.BdRp l, T.eD (c i j) = ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w' :=
    fun i j => hF _ _ ((T.fil K _ _).1 (hc i j))
  choose w' hw' using hW
  have hq : ∀ j, 0 ≤ h j + ((∑ j, (h j).natAbs : ℕ) : ℤ) := by
    intro j
    have h1 : (h j).natAbs ≤ ∑ j, (h j).natAbs := Finset.single_le_sum (f := fun j => (h j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcan : ∀ j, ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) = 1 := by
    intro j
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have hVW : (Matrix.of fun i j => w j i) * (Matrix.of fun j i => w' i j) = 1 := by
    ext k i
    apply hinj
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y k)) (hsum i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul]
    have e2 : ∀ j, T.eD (c i j) * T.eD (x j k) = algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j) := by
      intro j
      rw [hw, hw']
      linear_combination (algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j)) * hcan j
    simp only [e2] at e1
    rw [← e1, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  have hz : ∀ z : ℤ_[l], T.eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) =
      ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) (zOm l z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hfit.o]
    rfl
  refine ⟨{ V := Matrix.of fun i j => w j i
            unit := ⟨⟨_, _, hVW, _root_.mul_eq_one_comm.mp hVW⟩, rfl⟩
            p := fun j => (h j + ((∑ j, (h j).natAbs : ℕ) : ℤ)).toNat
            q := ∑ j, (h j).natAbs
            Q := Matrix.of fun i j => T.eD (x j i)
            Q_eq := ?_
            inv := ?_ }, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    rw [hw, map_mul, map_pow, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_add, Int.toNat_of_nonneg (hq j), add_comm]
  · intro g _
    ext i j
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y i)) (hinv j g)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, T.actD, hz] at e1
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact e1
  · intro i
    simp only
    rw [Int.toNat_of_nonneg (hq i)]
    ring

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamilyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_structure_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  first | (exact @GlobalTheory.BKLim.hodge_of_adapted) | (exact GlobalTheory.BKLim.hodge_of_adapted) | (intros; apply GlobalTheory.BKLim.hodge_of_adapted  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntSpanImageLatticeRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntSpanImageLatticeRegular
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_zl_span_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)), Continuous r → ∃ (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Continuous ρ ∧ Reads ρ r b e ∧ LinearIndependent ℚ_[l] b ∧ ∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • (r h).val := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  have hz : ∀ c : ℤ_[l], zOm l c = algebraMap ℤ_[l] (Om l) c := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l) c).symm
  have hsm : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = zOm l c • x := by
    intro c x; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, hz]
  have hsq : ∀ (c : ℤ_[l]) (x : Matrix (Fin a) (Fin a) (Om l)), c • x = (c : ℚ_[l]) • x := by
    intro c x; rw [hsm]; ext i j; simp [Matrix.smul_apply, Algebra.smul_def, zOm]
  let v : Γ → Matrix (Fin a) (Fin a) (Om l) := fun h => (r h).val
  let M : Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) := Submodule.span ℤ_[l] (Set.range v)

  obtain ⟨t, ht⟩ := GlobalTheory.zl_span_image_finite l Γ a r hr
  have hfg : M.FG := by
    refine ⟨t.image v, le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image]; exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single h 1)
      have hvh : v h = f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
        rw [← hf', Finsupp.sum_single_index (by simp)]
        simp [v]
      rw [SetLike.mem_coe, hvh]
      refine Submodule.sum_mem _ fun k hk => ?_
      have : ((algebraMap ℚ_[l] (PadicAlgCl l)) (f' k : ℚ_[l])) •
          ((r k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) = f' k • v k := by
        rw [hsm]; rfl
      refine (show _ ∈ _ from ?_)
      beta_reduce
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v (hf't hk))))
  haveI : Module.Finite ℤ_[l] M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree ℤ_[l] M := Module.IsTorsionFree.of_smul_eq_zero fun c m h => by
    have h' : (c : ℚ_[l]) • (m : Matrix (Fin a) (Fin a) (Om l)) = 0 := by
      rw [← hsq]; exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0
  haveI : Module.Free ℤ_[l] M := Module.free_of_finite_type_torsion_free'
  let d := Module.finrank ℤ_[l] M
  let B : Module.Basis (Fin d) ℤ_[l] M := Module.finBasis ℤ_[l] M

  have hstab : ∀ (g : Γ) (x : Matrix (Fin a) (Fin a) (Om l)), x ∈ M → v g * x ∈ M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      exact Submodule.subset_span ⟨g * h, by simp [v, map_mul]⟩
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.mul_add]; exact M.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact M.smul_mem c hy
  let Lm : Γ → Module.End ℤ_[l] M := fun g =>
    { toFun := fun x => ⟨v g * x, hstab g x x.2⟩
      map_add' := fun x y => Subtype.ext (Matrix.mul_add _ _ _)
      map_smul' := fun c x => Subtype.ext (Matrix.mul_smul _ _ _) }
  let L : Γ →* Module.End ℤ_[l] M :=
    { toFun := Lm
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp [Lm, v])
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp [Lm, v, map_mul, Matrix.mul_assoc]) }
  let ρ₀ : Γ →* Matrix (Fin d) (Fin d) ℤ_[l] :=
    (LinearMap.toMatrixAlgEquiv B).toAlgHom.toRingHom.toMonoidHom.comp L
  let ρ : Γ →* GL (Fin d) ℤ_[l] := ρ₀.toHomUnits
  have hρ : ∀ g i j, (ρ g).val i j = B.repr (Lm g (B j)) i := by
    intro g i j
    exact LinearMap.toMatrixAlgEquiv_apply B (L g) i j
  let b : Fin d → Matrix (Fin a) (Fin a) (Om l) := fun i => (B i : Matrix (Fin a) (Fin a) (Om l))
  have hrepr : ∀ x : M, ∑ i, zOm l (B.repr x i) • b i = x := by
    intro x
    have := congrArg Subtype.val (B.sum_repr x)
    rw [Submodule.coe_sum] at this
    simpa [b, hsm] using this
  have h1M : (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ M := Submodule.subset_span ⟨1, by simp [v]⟩
  let e : Fin d → ℤ_[l] := fun i => B.repr ⟨1, h1M⟩ i
  have hreads : Reads ρ r b e := by
    refine ⟨fun g j => ?_, ?_⟩
    · simp_rw [hρ]
      rw [hrepr]
      rfl
    · exact hrepr ⟨1, h1M⟩

  have hliZ : LinearIndependent ℤ_[l] b := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent ℚ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hliZ
  refine ⟨d, ρ, b, e, ?_, hreads, hli, fun i => ?_⟩
  rotate_left
  · obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (B i).2
    refine ⟨f, ?_⟩
    show (B i : Matrix (Fin a) (Fin a) (Om l)) = _
    rw [← hf]
    simp [Finsupp.sum, hsm, v]

  let Wq := Submodule.span ℚ_[l] (Set.range b)
  let Bq : Module.Basis (Fin d) ℚ_[l] Wq := Module.Basis.span hli
  haveI : FiniteDimensional ℚ_[l] Wq := Module.Finite.of_basis Bq
  have hmemW : ∀ x : M, (x : Matrix (Fin a) (Fin a) (Om l)) ∈ Wq := by
    intro x
    rw [← hrepr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsm, hsq]
    exact Wq.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcoord : ∀ x : M, ∀ i, ((B.repr x i : ℤ_[l]) : ℚ_[l]) = Bq.repr ⟨x, hmemW x⟩ i := by
    intro x i
    have hx : (⟨x, hmemW x⟩ : Wq) = ∑ k, ((B.repr x k : ℤ_[l]) : ℚ_[l]) • Bq k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_lhs => rw [← hrepr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, Module.Basis.span_apply, ← hsm, hsq]
    rw [hx, Module.Basis.repr_sum_self]
  have hcv : Continuous v := Units.continuous_val.comp hr
  have hval : Continuous fun g => (ρ g).val := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) = fun g => Bq.coord i ⟨v g * b j, hmemW (Lm g (B j))⟩ := by
      funext g
      rw [hρ, hcoord]
      rfl
    have hcq : Continuous (fun g => (((ρ g).val i j : ℤ_[l]) : ℚ_[l])) := by
      rw [this]
      refine (LinearMap.continuous_of_finiteDimensional (Bq.coord i)).comp ?_
      exact (hcv.mul continuous_const).subtype_mk _
    exact continuous_induced_rng.2 hcq
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun g => ((ρ g)⁻¹ : GL (Fin d) ℤ_[l]).val) = (fun g => (ρ g).val) ∘ fun g => g⁻¹ := by
    funext g; simp [map_inv]
  rw [this]
  exact hval.comp continuous_inv

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntSpanImageLatticeRegularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_span_image_lattice_regular : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)), Continuous r → ∃ (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Continuous ρ ∧ Reads ρ r b e ∧ LinearIndependent ℚ_[l] b ∧ ∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • (r h).val := by
  first | exact @GlobalTheory.BKLim.exists_zl_span_lattice_reads | exact GlobalTheory.BKLim.exists_zl_span_lattice_reads | (intros; apply GlobalTheory.BKLim.exists_zl_span_lattice_reads; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLocalIff
open IsDedekindDomain NumberField

namespace GlobalTheory.LocalSpanCriterion

theorem span_local_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module (RingOfIntegers K) V] (w : HeightOneSpectrum (RingOfIntegers K))
    [Module (Formalism.L2.Col.Ow w) V] [IsScalarTower (RingOfIntegers K) (Formalism.L2.Col.Ow w) V]
    (T : Set V) (x : V) :
    x ∈ Submodule.span (Formalism.L2.Col.Ow w) T ↔
      x ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) := by
  have hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) ↔
      ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T := fun y => Iff.rfl
  rw [hmem]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
      have e : (s * t) • (y + z) = t • (s • y) + s • (t • z) := by
        rw [smul_add, mul_smul, smul_comm s t y, mul_smul]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl a
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩
      have hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) *
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) =
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r := IsLocalization.mk'_spec _ r t
      simp only at hrt
      rw [hrt] at hspec
      have e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y) := by
        have ht : (t : RingOfIntegers K) • (a • y) = r • y := by
          rw [← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul,
            mul_comm, hspec, algebraMap_smul]
        rw [mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]
      rw [e]
      exact Submodule.smul_mem _ r hsy
  · rintro ⟨s, hs, hsx⟩
    have hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s) :=
      IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    have h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T := by
      have := Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx
      exact this
    rw [← algebraMap_smul (Formalism.L2.Col.Ow w) s x] at h1
    obtain ⟨u, hu'⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

end GlobalTheory.LocalSpanCriterion
end

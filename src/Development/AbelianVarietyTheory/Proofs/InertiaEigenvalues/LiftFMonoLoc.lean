module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsInVOfIsSubFam
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem jumpsInV_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (U : Set ℤ), (∀ x, JumpsInV (P.PD K) (matRep (Ms x)) τ U) → JumpsInV (P.PD K) W.ρ τ U := by
  intro l _ P K LL ι k Ms W hW τ U hU
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) W.ρ Ms τ U ⟨a, x, LinearMap.pi p, ?_, ?_⟩ hU
  · rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  · intro g v
    funext j
    exact hp j g v

end GlobalTheory.Pass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfIsSubFam
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvectorMemOfSumMem
namespace GlobalTheory.EigenvectorOfSum

theorem eigenvector_mem_of_sum_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ (g : I), ∀ y ∈ U, (T g : Y → Y) y ∈ U) (S : Finset α) (y : α → Y)
    (hy : ∀ a ∈ S, ∀ (g : I), (T g : Y → Y) (y a) = χ a g • y a)
    (hs : ∑ a ∈ S, y a ∈ U) : ∀ a ∈ S, y a ∈ U := by
  classical
  induction S using Finset.strongInduction generalizing y with
  | H S ih =>
  intro a ha
  by_cases hex : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, χ a g ≠ χ b g := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hba (hχ (funext hcon)).symm
    set y' : α → Y := fun c => (χ c g - χ b g) • y c with hyq
    have hy' : ∀ c ∈ S.erase b, ∀ g', (T g' : Y → Y) (y' c) = χ c g' • y' c := by
      intro c hc g'
      rw [hyq, map_smul, hy c (Finset.mem_of_mem_erase hc) g', smul_comm]
    have hs' : ∑ c ∈ S.erase b, y' c ∈ U := by
      have h1 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c ∈ U :=
        U.sub_mem (hU g _ hs) (U.smul_mem _ hs)
      have h2 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c = ∑ c ∈ S.erase b, y' c := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hb]
        have hb0 : (T g : Y → Y) (y b) - χ b g • y b = 0 := by rw [hy b hb g, sub_self]
        rw [hb0, add_zero]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hyq]
        dsimp only
        rw [sub_smul, hy c (Finset.mem_of_mem_erase hc) g]
      rwa [h2] at h1
    have hmem := ih (S.erase b) (Finset.erase_ssubset hb) y' hy' hs' a
      (Finset.mem_erase.2 ⟨hba.symm, ha⟩)
    have hne : χ a g - χ b g ≠ 0 := sub_ne_zero.2 hg
    have h3 := U.smul_mem (χ a g - χ b g)⁻¹ hmem
    rwa [hyq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
  · simp only [ne_eq, not_exists, not_and, not_not] at hex
    have hS : S = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hex⟩
    subst hS
    simpa using hs

end GlobalTheory.EigenvectorOfSum
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory

theorem subIner_component_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ g, ∀ y ∈ U, T g y ∈ U) (S : Finset α) :
    ∀ y : α → Y, (∀ a ∈ S, ∀ g, T g (y a) = χ a g • y a) → ∑ a ∈ S, y a ∈ U → ∀ a ∈ S, y a ∈ U := by
  first
  | exact @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | (apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem ..)

theorem subIner_pullback {L X Y I α J : Type} [Field L] [AddCommGroup X] [Module L X]
    [AddCommGroup Y] [Module L Y] (T : I → X →ₗ[L] X) (T' : J → I → Y →ₗ[L] Y)
    (m : J → X →ₗ[L] Y) (hm : ∀ j g x, m j (T g x) = T' j g (m j x))
    (hinj : ∀ x, (∀ j, m j x = 0) → x = 0)
    (χ : α → I → L) (hχ : Function.Injective χ) (D : Submodule L X)
    (hD : ∀ g, ∀ x ∈ D, T g x ∈ D) (S : Finset α) (d : X) (hd : d ∈ D)
    (y : J → α → Y) (hy : ∀ j, ∀ a ∈ S, ∀ g, T' j g (y j a) = χ a g • y j a)
    (hs : ∀ j, ∑ a ∈ S, y j a = m j d) :
    ∃ x : α → X, (∀ a ∈ S, x a ∈ D ∧ ∀ g, T g (x a) = χ a g • x a) ∧ ∑ a ∈ S, x a = d := by
  classical
  have key := subIner_component_mem (Y := J → Y)
    (fun g => LinearMap.pi fun j => (T' j g).comp (LinearMap.proj j)) χ hχ (D.map (LinearMap.pi m))
    (by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨T g x, hD g x hx, by ext j; simp [hm]⟩) S (fun a j => y j a)
    (fun a ha g => by ext j; simp [hy j a ha g])
    ⟨d, hd, by ext j; simp [← hs j, Finset.sum_apply]⟩
  have h1 : ∀ a, ∃ x : X, a ∈ S → x ∈ D ∧ ∀ j, m j x = y j a := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨x, hx, e⟩ := key a ha
      exact ⟨x, fun _ => ⟨hx, fun j => congrFun e j⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose x hx using h1
  refine ⟨x, fun a ha => ⟨(hx a ha).1, fun g => ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, hm, map_smul, (hx a ha).2, hy j a ha, sub_self]
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← hs j, sub_eq_zero]
    exact Finset.sum_congr rfl fun a ha => (hx a ha).2 j

theorem subIner_rTensor_inj {Qp LL B V U : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [AddCommGroup B] [Module Qp B]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {n : ℕ} (p : Fin n → V →ₗ[LL] U) (hp : ∀ v, (∀ j, p j v = 0) → v = 0) (x : V ⊗[Qp] B)
    (hx : ∀ j, AlgebraTensorModule.rTensor Qp B (p j) x = 0) : x = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.pi p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun v hv => hp v fun j => congrFun hv j)
  have h1 : ∀ v, ∑ j, q (Pi.single j (p j v)) = v := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
    exact LinearMap.congr_fun hq v
  have h2 : ∀ z : V ⊗[Qp] B, ∑ j, AlgebraTensorModule.rTensor Qp B
      (q.comp (LinearMap.single LL (fun _ => U) j)) (AlgebraTensorModule.rTensor Qp B (p j) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_rhs => rw [← h1 v, TensorProduct.sum_tmul]
      simp
    | add z w hz hw => simp only [map_add (f := _), Finset.sum_add_distrib, hz, hw]
  rw [← h2 x]
  simp [hx]

section General

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
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem subIner_mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h ∈ PC.H, actVB PC.PD ρ h x = x := by
  have h1 : ∀ (h : PC.H) (z : V ⊗[Qp] B), actVB PC.PD' (PC.resH ρ) h z = actVB PC.PD ρ h z := by
    intro h z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  simp [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, sub_eq_zero, h1]

theorem subIner_actVB_mul (ρ : Representation LL G V) (g h : G) (z : V ⊗[Qp] B) :
    actVB PC.PD ρ g (actVB PC.PD ρ h z) = actVB PC.PD ρ (g * h) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

theorem subIner_Dpcris_stable (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) : actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [subIner_mem_Dpcris] at hx ⊢
  intro h hh
  have h1 := hx (g⁻¹ * h * g⁻¹⁻¹) (PC.normal.conj_mem h hh g⁻¹)
  conv_rhs => rw [← h1]
  rw [subIner_actVB_mul, subIner_actVB_mul]
  congr 2
  group

theorem subIner_rTensor_actVB (ρ : Representation LL G V) (σ : Representation LL G U)
    (f : V →ₗ[LL] U) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (z : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PC.PD ρ g z) =
      actVB PC.PD σ g (AlgebraTensorModule.rTensor Qp B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

theorem subIner_mem_Eig (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ) (x : V ⊗[Qp] B) :
    x ∈ PC.Eig ρ I a ↔ x ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ g x = ((a g : LLˣ) : LL) • x := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, sub_eq_zero]

theorem subIner_Dpcris_eq (ρ : Representation LL G V) {n : ℕ} (σ : Fin n → Representation LL G U)
    (p : Fin n → V →ₗ[LL] U) (hp : ∀ j g v, p j (ρ g v) = σ j g (p j v))
    (hinj : ∀ v, (∀ j, p j v = 0) → v = 0) (I : Subgroup G) (Sig : Finset (I →* LLˣ))
    (hσ : ∀ j, PC.Dpcris (σ j) = ⨆ a ∈ Sig, PC.Eig (σ j) I a) :
    PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ I a := by
  refine le_antisymm (fun d hd => ?_) (iSup₂_le fun a _ => inf_le_left)
  have h1 : ∀ j, ∃ μ : ∀ a, PC.Eig (σ j) I a,
      ∑ a ∈ Sig, (μ a : U ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B (p j) d := by
    intro j
    rw [← Submodule.mem_iSup_finset_iff_exists_sum, ← hσ j, subIner_mem_Dpcris]
    intro h hh
    rw [← subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j), (subIner_mem_Dpcris PC ρ d).1 hd h hh]
  choose μ hμ using h1
  obtain ⟨x, hx, rfl⟩ := subIner_pullback (fun g : I => actVB PC.PD ρ g)
    (fun j (g : I) => actVB PC.PD (σ j) g) (fun j => AlgebraTensorModule.rTensor Qp B (p j))
    (fun j g z => subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j) g z)
    (subIner_rTensor_inj p hinj) (fun (a : I →* LLˣ) g => ((a g : LLˣ) : LL))
    (fun a b hab => MonoidHom.ext fun g => Units.ext (congrFun hab g)) (PC.Dpcris ρ)
    (fun g z hz => subIner_Dpcris_stable PC ρ g z hz) Sig d hd (fun j a => μ j a)
    (fun j a _ g => ((subIner_mem_Eig PC (σ j) I a _).1 (μ j a).2).2 g) hμ
  refine Submodule.sum_mem _ fun a ha => ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
    ((subIner_mem_Eig PC ρ I a _).2 (hx a ha)))

end General

theorem inertiaThrough_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p) → (∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig) → (pc P h hN hF hS).InertiaThrough W.ρ Sig := by
  intro l _ P K K' LL h hN hF hS ι k Ms W hW Sig h1 h2 h3
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine ⟨h1, h2, ?_⟩
  exact subIner_Dpcris_eq (pc P h hN hF hS) W.ρ (fun j => matRep (Ms (x j))) p
    (fun j g v => by rw [hp]; simp [matRep]) hinj _ Sig fun j => (h3 (x j)).2.2

end GlobalTheory

end
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.StepLiftPf

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem liftF_mono {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

section MonoLoc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_mono_loc {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' :=
  liftF_mono PD F hF he

end MonoLoc

section Core

variable {l : ℕ} [Fact l.Prime]

theorem incl_cont {K K' : FinExt l} (h : K.1 ≤ K'.1) : Continuous (Subgroup.inclusion (GK_le h)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem sub_props (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x))
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ))
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Set ℤ) (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ U)
    (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hW : IsSubFam Ms W) :
    (pc P h hN hF hS).IsPotCrys W.ρ ∧ (pc P h hN hF hS).InertiaThrough W.ρ Sig ∧
      ∀ τ, JumpsInV (P.PD K) W.ρ τ U := by
  refine ⟨?_, GlobalTheory.inertiaThrough_of_isSubFam l P K K' LL h hN hF hS ι k Ms W hW Sig htr hcop hin,
    fun τ => GlobalTheory.Pass.jumpsInV_of_isSubFam l P K LL ι k Ms W hW τ U fun x => hJ x τ⟩
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := incl_cont h
  let W' : GRep ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W.V, ρ := W.ρ.comp incl, cont := fun x => (W.cont x).comp hincl }
  let Ms' : ι → (↥(GK K') →* Matrix (Fin k) (Fin k) ↥LL.1) := fun x => (Ms x).comp incl
  have hc' : ∀ x v, Continuous fun g => (Ms' x g).mulVec v :=
    fun x v => ((hc x).comp hincl).matrix_mulVec continuous_const
  have hcr' : ∀ x, IsCrys (P.PD K') (matRep (Ms' x)) := fun x =>
    (GlobalTheory.PcRes.main l P K K' LL h hN hF hS _ (matRep (Ms x))).2.1 (hpot x)
  have hsub : IsSubOfSums W'.ρ (fun x => ⇑(Ms' x)) := by
    obtain ⟨a, x, p, hp, hinj⟩ := hW
    refine ⟨a, x, LinearMap.pi p, ?_, fun g v => funext fun j => hp j (incl g) v⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  have hW' : IsCrys (P.PD K') W'.ρ :=
    (subsum_crys (PD := P.PD K') (Ms := Ms') (hc := hc') (hF := hFont) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact (GlobalTheory.PcRes.main l P K K' LL h hN hF hS W.V W.ρ).2.2 hW'

end Core

section Apply

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
theorem liftFam_core (P : LocPrime l) (K' LL : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (CT : ℕ) (hT : thmT (pc P h hN hF hS) LL CT)
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK (qlExt l)) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l)))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK (qlExt l))) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD (qlExt l)) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD (qlExt l)) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  intro W₁ W₂ hW₁ hW₂ L₁ L₂ F hFo
  have k₁ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₁ hW₁
  have k₂ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₂ hW₂
  let T₁ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₁.V, modO := W₁.modO, towO := W₁.towO, ρ := W₁.ρ, cont := W₁.cont, L := L₁ }
  let T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₂.V, modO := W₂.modO, towO := W₂.towO, ρ := W₂.ρ, cont := W₂.cont, L := L₂ }
  obtain ⟨h4, hL⟩ := hT T₁ T₂ F N η H U Sig Fr k₁.1 k₂.1 hFo hFr hSt h1 hcard hN2 k₁.2.1 k₂.2.1 hU hU0
    hUc hη hηH k₁.2.2 k₂.2.2 hsize
  have hr : rPrime (pc P h hN hF hS).Iner Fr Sig ≤ N ^ 2 / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [mul_comm]; exact h4)
  have he : CT * (N * rPrime (pc P h hN hF hS).Iner Fr Sig + η * (N + rPrime (pc P h hN hF hS).Iner Fr Sig)) ≤
      CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4)) := by
    gcongr
  exact liftF_mono_loc (P.PD (qlExt l)) (T₁ := T₁) (T₂ := T₂) F hL he

end Apply

section Wrap

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
theorem liftFam_of_eq (P : LocPrime l) (K K' LL : FinExt l) (hK : K = qlExt l) (CT : ℕ)
    (hT : ∀ (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
      thmT (pc P h hN hF hS) LL CT)
    (hFont : ∀ K'' : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt (P.PD K'') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK K))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (hx : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)) ∧
      (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD K) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  subst hK
  by_cases hne : Nonempty ι
  · obtain ⟨x0⟩ := hne
    exact liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      Sig Fr hFr hSt h1 hcard (hx x0).2.1 (hx x0).2.2.1 (fun x => (hx x).1) (fun x => (hx x).2)
      U hU hU0 hUc hJ
  · have hemp : ∀ x : ι, False := fun x => hne ⟨x⟩
    refine liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      {1} Fr hFr ?_ (Finset.mem_singleton_self _) (by rw [Finset.card_singleton]; omega) ?_ ?_
      (fun x => (hemp x).elim) (fun x => (hemp x).elim) U hU hU0 hUc hJ
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨1, Finset.mem_singleton_self _, fun _ _ _ => rfl⟩
    · intro a ha g _
      rw [Finset.mem_singleton] at ha
      subst ha
      rfl
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [orderOf_one]
      exact Nat.coprime_one_left _

end Wrap

theorem main : StepLift := by
  intro D CT hT hFont i w hw hdeg ι Ms hc eta H hlt hsize hPot hJump
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hSt, h1, hcard, hx⟩ := hPot
  obtain ⟨U, hU, hU0, hUc, hJ⟩ := hJump
  have hK : (D.nbr i w hw).Kw = Formalism.MainNotions.ElementDenominator.qlExt (D.nd.l i) :=
    Subtype.ext (IntermediateField.finrank_eq_one_iff.1 hdeg)
  have hT' : Formalism.MainNotions.ElementDenominator.CorollaryALocal D.loc CT := hT
  have hnV : 2 ≤ D.R.nV + 1 := by
    have h5 := D.R.rank_add_five_le
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hcl : ∀ x, Continuous (Br.loc D.nbr i w hw (Ms x)) := by
    intro x
    have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h1' : Continuous fun g : Br.G D.nbr i w hw => Ms x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
      (hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    exact h1'.matrix_map hfc
  exact liftFam_of_eq (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK CT
    (fun K' h hN hF hS => hT' (D.nd.l i) K' h hN hF hS (D.nbr i w hw).LL)
    (fun K'' => hFont (D.nd.l i) K'' (D.nbr i w hw).LL)
    (fun x => Br.loc D.nbr i w hw (Ms x)) hcl (D.R.nV + 1) (eta + D.R.t + 1) H hnV (by omega) hlt hsize
    h hN hF hS Sig Fr hFr hSt h1 hcard hx U hU hU0 hUc hJ

end GlobalTheory.StepLiftPf

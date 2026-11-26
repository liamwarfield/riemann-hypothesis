module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfKernelPowerClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

section TwistDeRham

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem deRhamTwist_galoisAct_period (g : G) :
    PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := by
  rw [← PD.ι_comm, PD.t_act, ← algebraMap_smul K₀ ((PD.χ g : Qpˣ) : Qp) PD.t, map_smul,
    algebraMap_smul]

theorem drTwist_pow_mem (e : ℕ) : (PD.ι PD.t) ^ e ∈ PD.Fil (e : ℤ) := by
  induction e with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact_mod_cast PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one

theorem drTwist_Fil_le (e : ℕ) : PD.Fil (e : ℤ) ≤ PD.Fil 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    exact_mod_cast PD.Fil_anti (n : ℤ)

noncomputable def drTwistMap (e : ℕ) : K →ₗ[Qp] BdR :=
  (LinearMap.mulRight Qp ((PD.ι PD.t) ^ e)) ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem drTwistMap_apply (e : ℕ) (k : K) :
    drTwistMap PD e k = algebraMap K BdR k * (PD.ι PD.t) ^ e := rfl

theorem drTwistMap_injective (e : ℕ) : Function.Injective (drTwistMap PD e) := by
  have hnt : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact PD.not_mem_filtration_two (by rw [Subsingleton.elim (PD.ι PD.t) 0]; exact Submodule.zero_mem _)
  intro a b hab
  rw [drTwistMap_apply, drTwistMap_apply] at hab
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  exact (algebraMap K BdR).injective (hu.mul_right_cancel hab)

theorem drTwistMap_mem (e : ℕ) (k : K) : drTwistMap PD e k ∈ PD.Fil 0 := by
  rw [drTwistMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (drTwist_Fil_le PD e (drTwist_pow_mem PD e))

theorem drTwist_act_pow (e : ℕ) (g : G) :
    PD.actdR g ((PD.ι PD.t) ^ e) = ((PD.χ g : Qpˣ) : Qp) ^ e • (PD.ι PD.t) ^ e := by
  rw [map_pow, deRhamTwist_galoisAct_period, smul_pow]

theorem drTwistMap_fixed (e : ℕ) (g : G) (k : K) :
    (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (drTwistMap PD e k) = drTwistMap PD e k := by
  rw [drTwistMap_apply, map_mul, AlgEquiv.commutes, drTwist_act_pow, mul_smul_comm, smul_smul,
    ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul]

theorem drTwistMap_range (e : ℕ) (y : BdR)
    (hy : ∀ g, (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y = y) :
    ∃ k, drTwistMap PD e k = y := by
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  have hyz : y = (y * z) * (PD.ι PD.t) ^ e := by rw [mul_assoc, hz, mul_one]
  obtain ⟨k, hk⟩ := PD.invdR (y * z) (fun g => by
    apply hu.mul_right_cancel
    have h := hy g
    rw [hyz, map_mul, drTwist_act_pow, mul_smul_comm, smul_smul,
      ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul] at h
    exact h)
  exact ⟨k, by rw [drTwistMap_apply, hk, ← hyz]⟩

variable {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V)

theorem drTwist_act_tmul (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (g : G) (v : V) (y : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] y) =
      v ⊗ₜ[Qp] ((((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y) := by
  have : actVdR PD ρ g (v ⊗ₜ[Qp] y) = ρ g v ⊗ₜ[Qp] PD.actdR g y := rfl
  rw [this, h, ← map_inv₀, ← map_pow, algebraMap_smul, smul_tmul]

theorem drTwist_range (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) =
      DdR PD ρ := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, AlgebraTensorModule.map_tmul, sub_eq_zero]
      intro g
      rw [drTwist_act_tmul PD ρ e h, drTwistMap_fixed]
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp V
    let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have hE : ∀ g (x : V ⊗[Qp] BdR) i, E (actVdR PD ρ g x) i =
        (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (E x i) := by
      intro g x i
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb, smul_add]
      | tmul v y =>
        rw [drTwist_act_tmul PD ρ e h]
        simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        rw [← algebraMap_smul K (b.repr v i) y, map_smul, algebraMap_smul, smul_comm]
    have hx' : x = E.symm (E x) := (E.symm_apply_apply x).symm
    rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    obtain ⟨k, hk⟩ := drTwistMap_range PD e (E x i) (fun g => by rw [← hE, hx g])
    exact ⟨b i ⊗ₜ k, by rw [AlgebraTensorModule.map_tmul, hk]; rfl⟩

end TwistDeRham

theorem isDR_and_DdR_le_Fil_zero_of_twist : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (e : ℕ), (∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) → IsDR PD ρ ∧ DdR PD ρ ≤ FilV PD (LL := LL) (V := V) 0 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ _ ρ e h
  have hr := drTwist_range PD ρ e h
  constructor
  · have hinj : Function.Injective
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ (drTwistMap_injective PD e)
    have := PD.finK
    unfold IsDR
    rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct, mul_comm]
  · rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k => exact ⟨v ⊗ₜ ⟨drTwistMap PD e k, drTwistMap_mem PD e k⟩, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePair
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePair
noncomputable section
namespace GlobalTheory.TopSteps.ExtPair
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem exists_proj {m m' : ℕ} (hm : m' = m + 1) (a : (Fin m → k) →ₗ[k] (Fin m' → k)) (e : Fin m' → k)
    (ha : Function.Injective a) (he : e ∉ LinearMap.range a) :
    ∃ p : (Fin m' → k) →ₗ[k] (Fin 1 → k), Function.Exact a p ∧ p e = (fun _ => 1) ∧ Function.Surjective p := by
  obtain ⟨f, hf, hfe⟩ := LinearMap.exists_extend_of_notMem (0 : LinearMap.range a →ₗ[k] k) he 1
  have hfs : Function.Surjective f := fun c => ⟨c • e, by simp [hfe]⟩
  have hle : LinearMap.range a ≤ LinearMap.ker f := fun x hx => by
    simpa using LinearMap.congr_fun hf ⟨x, hx⟩
  have h1 := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hfs] at h1
  have h2 := LinearMap.finrank_range_of_inj ha
  simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1 h2
  have heq : LinearMap.range a = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨LinearMap.pi fun _ => f, fun x => ?_, funext fun _ => hfe, fun y => ?_⟩
  · change _ ↔ x ∈ LinearMap.range a
    rw [heq, LinearMap.mem_ker]
    constructor
    · intro h; exact congrFun h 0
    · intro h; exact funext fun _ => h
  · obtain ⟨x, hx⟩ := hfs (y 0)
    exact ⟨x, funext fun j => by rw [Subsingleton.elim j 0]; exact hx⟩

theorem mem_sh_comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ) (x : Vc k a) :
    x ∈ sh s (N.comap (φ.restrictScalars k⟦X⟧)) ↔ φ x ∈ sh s N := by
  rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]; rfl

theorem aeval_nab_mem {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (N : Submodule k⟦X⟧ (Vc k a)) (hN : CondC g N)
    (f : Polynomial k) (x : Vc k a) (hx : x ∈ N) : Polynomial.aeval (nab g) f x ∈ N := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact N.smul_of_tower_mem c hx
  | add p q hp hq =>
    simp only [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem (hp x hx) (hq x hx)
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ ((condC_iff_nab_mem g N).1 hN x hx)

theorem aeval_nab_fixed {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (f : Polynomial k) (u : Vc k a) (hu : g u = u) :
    Polynomial.aeval (nab g) f u = f.eval 0 • u := by
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  rw [nab_apply_eq, hu, sub_self, smul_zero, zero_smul]

theorem exists_model_repr_inZZ : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l →
    ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A →
      ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A z hz
  obtain ⟨E, NE, ⟨hm, a, e, ha, hai, he, hez⟩, hNE⟩ := hz
  obtain ⟨p, hex, hpe, hps⟩ := exists_proj hm a e hai he
  have hpa : ∀ y, p (a y) = 0 := hex.apply_apply_eq_zero
  have hp : IsHom E (chr 1) p := by
    intro σ x
    obtain ⟨y, hy⟩ := (hex (x - p x 0 • e)).1 (by
      rw [map_sub, map_smul, hpe]; funext j; rw [Subsingleton.elim j 0]; simp)
    have hx : x = a y + p x 0 • e := by rw [hy]; abel
    have h : p (E.ρ σ x) = p x := by
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_add (f := _), map_smul, ← ha, hez]
      simp only [map_add (f := _), map_smul, hpa, add_zero]
    rw [h]
    change _ = (((1 : G →* kˣ) σ : kˣ) : k) • p x
    simp
  obtain ⟨oE, -, hAB, hC⟩ := GlobalTheory.T.obj_and_abc_of_model F M E NE hNE
  have oA := F.obj_sub A E a ha hai oE
  have o1 := F.obj_one
  have hq : M.Model (chr 1) (F.push E (chr 1) p NE) :=
    GlobalTheory.Models.ModTh.model_push_of_surjective F M E (chr 1) p NE hp hps hNE
  have hq' : ∀ χ : G →* kˣ, χ = 1 → M.Model (chr χ) (F.push E (chr 1) p NE) := by
    rintro _ rfl; exact hq
  have hpush : ∀ i, F.push E (chr 1) p NE i = Submodule.span k⟦X⟧ {F.unit i} := fun i => by
    rw [← M.χ_zero i]
    exact congrFun (GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl (by exact_mod_cast Dt.one_le_letterBlockLength) _
      (hq' _ (by simp))) i
  have hε : ∀ i, ∃ ε ∈ NE i, F.map E (chr 1) p i ε = F.unit i := fun i => by
    have : F.unit i ∈ F.push E (chr 1) p NE i := by
      rw [hpush]; exact Submodule.mem_span_singleton_self _
    exact this
  choose ε hεN hεp using hε
  have hD := GlobalTheory.Models.DFun.map_exact_middle F A E (chr 1) a p oE ha hp hai hps hex
  have hinj := F.map_inj A E a oA oE ha hai
  have aφ := F.map_φ A E a oA oE ha
  have aγ := F.map_γ A E a oA oE ha
  have pφ := F.map_φ E (chr 1) p oE o1 hp
  have pγ := F.map_γ E (chr 1) p oE o1 hp
  have hb : ∀ i, ∃ b, F.map A E a i b = (F.D E).φ i (ε (i - 1)) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pφ, hεp, hεp, F.unit_φ, sub_self])
  have hg : ∀ i, ∃ g, F.map A E a i g = (F.D E).γ i (ε i) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pγ, hεp, F.unit_γ, sub_self])
  choose b hb using hb
  choose g hg using hg
  refine ⟨F.pre A E a NE, b, g, GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A E a NE ha hai hNE,
    ⟨E, a, p, e, ε, oE, ha, hp, hai, hex, hpe, hez, fun i => ⟨hεp i, hb i, hg i⟩⟩, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · apply hinj i
    rw [map_sub, map_sub, aφ, aγ, hb, hg, hg, map_sub, map_sub, (F.D E).comm]
    abel
  · refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hg]; exact hC i _ (hεN i)
  · intro _
    refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hb]
    have hw : 1 ≤ Dt.w i := (Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2
      ⟨le_rfl, by have := Dt.one_le_letterBlockLength; omega⟩)))).1
    refine Submodule.sub_mem _ ((hAB i).1 (Submodule.subset_span ⟨_, hεN _, rfl⟩)) ?_
    apply sh_le_sh_of_le (a := 0) (by omega)
    rw [sh_zero_eq]; exact hεN i
  · intro hi
    constructor
    · have hdec : ∀ y ∈ pull ((F.D E).φ i) (NE (i - 1)), ∃ m ∈ pull ((F.D A).φ i) (F.pre A E a NE (i - 1)),
          ∃ c : k⸨X⸩, y = F.map A E a i m + c • (F.D E).φ i (ε (i - 1)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          have h4 : F.map E (chr 1) p (i - 1) x ∈ F.push E (chr 1) p NE (i - 1) := ⟨x, hx, rfl⟩
          rw [hpush, Submodule.mem_span_singleton] at h4
          obtain ⟨c, hc⟩ := h4
          obtain ⟨m, hm⟩ := (hD (i - 1) (x - c • ε (i - 1))).1 (by
            rw [map_sub, LinearMap.map_smul_of_tower, hεp, hc, sub_self])
          have hmN : m ∈ F.pre A E a NE (i - 1) := by
            change F.map A E a (i - 1) m ∈ NE (i - 1)
            rw [hm]; exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hεN _))
          refine ⟨(F.D A).φ i m, Submodule.subset_span ⟨m, hmN, rfl⟩, R.φ (algebraMap k⟦X⟧ k⸨X⸩ c), ?_⟩
          rw [aφ, hm, ← (F.D E).φ_semi i, algebraMap_smul, ← map_add (f := _), sub_add_cancel]
        | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
        | add y y' _ _ hy hy' =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          obtain ⟨m', hm', c', rfl⟩ := hy'
          exact ⟨m + m', Submodule.add_mem _ hm hm', c + c', by rw [map_add (f := _), add_smul]; abel⟩
        | smul d y _ hy =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          refine ⟨d • m, Submodule.smul_mem _ _ hm, d • c, ?_⟩
          rw [smul_add, LinearMap.map_smul_of_tower, smul_assoc]
      obtain ⟨m, hm, c, hc⟩ := hdec _ ((hAB i).2 (mem_sh_iff_exists.2 ⟨_, hεN i, rfl⟩))
      have h5 := congrArg (F.map E (chr 1) p i) hc
      rw [map_smul, map_add (f := _), map_smul, pφ, hεp, hεp, F.unit_φ, (hD i).apply_apply_eq_zero, zero_add] at h5
      have h6 : vv k ^ Dt.wst i = c := smul_left_injective _ (F.unit_ne i) h5
      rw [mem_sh_iff_smul_mem, neg_neg]
      have h7 : vv k ^ Dt.wst i • b i = -m := by
        apply hinj i
        rw [map_smul, hb, smul_sub, hc, h6, map_neg]; abel
      rw [h7]; exact Submodule.neg_mem _ hm
    · obtain ⟨f, hf, hfN⟩ := GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 E NE hNE i hi
      obtain ⟨x, hx⟩ := (hD i (ε i - (f.eval 0)⁻¹ • Polynomial.aeval (nab ((F.D E).γ i)) f (ε i))).1 (by
        rw [map_sub, LinearMap.map_smul_of_tower,
          EPolyModel.map_aeval_nab (F.map E (chr 1) p i) _ _ (pγ i), hεp, aeval_nab_fixed _ _ _ (F.unit_γ i),
          smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self])
      refine ⟨x, ?_, (mem_sh_comap _ _ _ _).2 ?_⟩
      · change F.map A E a i x ∈ NE i
        rw [hx]
        exact Submodule.sub_mem _ (hεN i)
          (Submodule.smul_of_tower_mem _ _ (aeval_nab_mem _ _ (hC i) f _ (hεN i)))
      · have h4 := hfN _ (hεN i)
        set y := Polynomial.aeval (nab ((F.D E).γ i)) f (ε i)
        have h5 : (F.D E).γ i y - y ∈ sh (Dt.wst i + 2) (NE i) := by
          rw [show Dt.wst i + 2 = 1 + (Dt.wst i + 1) by ring, ← sh_sh_eq, mem_sh_iff_smul_mem, zpow_neg_one]
          exact h4
        have h6 : F.map A E a i (g i - ((F.D A).γ i x - x)) = (f.eval 0)⁻¹ • ((F.D E).γ i y - y) := by
          rw [map_sub, map_sub, aγ, hg, hx, map_sub, map_smul, smul_sub]; abel
        rw [h6]
        exact Submodule.smul_of_tower_mem _ _ h5

end GlobalTheory.TopSteps.ExtPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePairStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A → ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  first | exact @GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | exact GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | (intros; apply GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussDefinite

theorem add_pow_split {R : Type} [CommRing R] (x p : R) (j m : ℕ) :
    ∃ u v : R, (x + p) ^ j = x ^ m * u + p ^ (j - m) * v := by
  induction j generalizing m with
  | zero => exact ⟨0, 1, by simp⟩
  | succ j ih =>
    rcases m with _ | m
    · exact ⟨(x + p) ^ (j + 1), 0, by simp⟩
    obtain ⟨u, v, h⟩ := ih m
    obtain ⟨u', v', h'⟩ := ih (m + 1)
    obtain ⟨d, hd⟩ : ∃ d, j - (m + 1) + 1 = j - m + d := ⟨j - (m + 1) + 1 - (j - m), by omega⟩
    refine ⟨u + p * u', x * v + p ^ d * v', ?_⟩
    rw [show j + 1 - (m + 1) = j - m by omega]
    have e : p * p ^ (j - (m + 1)) = p ^ (j - m) * p ^ d := by rw [← pow_add, ← hd, pow_succ']
    calc (x + p) ^ (j + 1) = x * (x + p) ^ j + p * (x + p) ^ j := by ring
      _ = x * (x ^ m * u + p ^ (j - m) * v) + p * (x ^ (m + 1) * u' + p ^ (j - (m + 1)) * v') := by
        rw [← h, ← h']
      _ = _ := by linear_combination v' * e

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_flat : ∃ x : Per.Fl l, x.untilt = (l : Per.OC l) := by
  have hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos
    have h1 : ‖b‖ ^ l ≤ 1 := by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2
    exact ⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩,
      Subtype.ext hb⟩
  choose r hr using hr
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] (l : Per.OC l)) (fun n => by
    rw [Function.iterate_succ_apply', hr])
  exact ⟨e, he 0⟩

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_root (x : Per.Fl l) (i : ℕ) :
    ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) =
      ‖(((((frobeniusEquiv (Per.Fl l) l).symm ^ i) x).untilt : Per.OC l) : ℂ_[l])‖ := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i
  have e : ((frobeniusEquiv (Per.Fl l) l).symm ^ i) x = ((frobeniusEquiv (Per.Fl l) l).symm)^[i] x := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Function.iterate_succ_apply', ← ih (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i)]; rfl
  rw [← h, e]
  push_cast
  rw [norm_pow, one_div, ← Nat.cast_pow, Real.pow_rpow_inv_natCast (norm_nonneg _)
    (pow_ne_zero _ hl.out.ne_zero)]

theorem split_of_small (a : Per.Ainf l) (M m : ℕ)
    (h : ∀ i : ℕ, ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤
      ((l : ℝ)⁻¹) ^ M) :
    ∃ c : Per.Ainf l, a - (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
  obtain ⟨w, hw⟩ := exists_flat l
  have hk : Per.tm w - (l : Per.Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, hw, sub_self]
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hl.out.pos)
  have key : ∀ i ∈ Finset.Iic M, ∃ c : Per.Ainf l,
      Per.tm (((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)) * (l : Per.Ainf l) ^ i -
        (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    have h1 := h i
    rw [norm_root] at h1
    set y := ((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)
    have h2 : ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (M - i) := by
      rw [norm_l]
      refine le_of_mul_le_mul_right ?_ (pow_pos hl0 i)
      rwa [← pow_add, Nat.sub_add_cancel hi]
    rw [← GlobalTheory.RingBasics.mem_span_pow_OC, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hw,
      ← map_pow] at h2
    obtain ⟨z, hz⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd h2
    obtain ⟨u, v, huv⟩ := add_pow_split (Per.tm w - (l : Per.Ainf l)) (l : Per.Ainf l) (M - i) m
    obtain ⟨d, hd⟩ : ∃ d, M - i - m + i = M - m + d := ⟨M - i - m + i - (M - m), by omega⟩
    have e : (l : Per.Ainf l) ^ (M - i - m) * (l : Per.Ainf l) ^ i =
        (l : Per.Ainf l) ^ (M - m) * (l : Per.Ainf l) ^ d := by rw [← pow_add, hd, pow_add]
    refine ⟨(l : Per.Ainf l) ^ d * v * Per.tm z, ?_⟩
    have e2 : Per.tm y * (l : Per.Ainf l) ^ i - (l : Per.Ainf l) ^ (M - m) * ((l : Per.Ainf l) ^ d * v * Per.tm z)
        = (Per.tm w - (l : Per.Ainf l)) ^ m * (u * Per.tm z * (l : Per.Ainf l) ^ i) := by
      rw [sub_add_cancel] at huv
      rw [hz, Per.tm, map_mul, map_pow]
      change Per.tm w ^ (M - i) * Per.tm z * _ - _ = _
      rw [huv]
      linear_combination (v * Per.tm z) * e
    rw [e2]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk m)
  choose! c hc using key
  obtain ⟨t, ht⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) a M
  obtain ⟨d, hd⟩ : ∃ d, M + 1 = M - m + d := ⟨M + 1 - (M - m), by omega⟩
  refine ⟨∑ i ∈ Finset.Iic M, c i + (l : Per.Ainf l) ^ d * t, ?_⟩
  have := Ideal.sum_mem _ hc
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  rw [hd, pow_add] at ht
  convert this using 1
  linear_combination ht

theorem map_mem_kerP (a : Per.Ainf l) (m : ℕ) (h : a ∈ RingHom.ker (Per.θ l) ^ m) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  have h1 : RingHom.ker (Per.θ l) ≤ (Per.kerP l).comap (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    intro x hx
    exact Ideal.mem_comap.2 (GlobalTheory.RingIface.alg_mem_kerP l (RingHom.mem_ker.1 hx))
  exact Ideal.le_comap_pow _ m (Ideal.pow_right_mono h1 m h)

theorem term_le_one (a : Per.Ainf l) (i : ℕ) :
    ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤ 1 := by
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
  rw [norm_root]
  exact mul_le_one₀ ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _)) (by positivity)
    (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1))

theorem gauss_pow_le (k : ℕ) :
    ⨆ i : ℕ, ‖(((((l : Per.Ainf l) ^ k).coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) *
      ((l : ℝ)⁻¹) ^ i ≤ ((l : ℝ)⁻¹) ^ k := by
  refine ciSup_le fun i => ?_
  rw [norm_root]
  by_cases h : i = k
  · subst h
    exact mul_le_of_le_one_left (by positivity) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _))
  · have h0 : (0 : Per.Fl l).untilt = 0 := by
      rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
    rw [WittVector.coeff_p_pow_eq_zero _ _ h, map_zero, h0]
    simp

theorem envelope_split (N : Per.Acris l → ℝ) (h0 : ∀ x, 0 ≤ N x) (hm : ∀ x y, N (x * y) = N x * N y)
    (hA : ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n)
    (s : Per.Acris0 l) (k m : ℕ) (hs : N (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m)) :
    ∃ c : Per.Ainf l, (s : Per.AinfP l) - algebraMap (Per.Ainf l) (Per.AinfP l) ((l : Per.Ainf l) ^ k * c) ∈
      Per.kerP l ^ m := by
  obtain ⟨K, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have e0 : s * algebraMap (Per.Ainf l) (Per.Acris0 l) ((l : Per.Ainf l) ^ K) =
      algebraMap (Per.Ainf l) (Per.Acris0 l) a := Subtype.ext (by rw [← map_pow] at ha; exact ha)
  have hc : ∀ x, algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) x := fun x => (GlobalTheory.RingIface.tower l x).symm
  have e1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e0
  rw [map_mul, hc, hc] at e1
  have hN : N (algebraMap (Per.Ainf l) (Per.Acris l) a) ≤ ((l : ℝ)⁻¹) ^ (k + m + K) := by
    rw [← e1, hm, pow_add]
    refine mul_le_mul hs ?_ (h0 _) (by positivity)
    rw [hA]
    exact gauss_pow_le l K
  rw [hA] at hN
  obtain ⟨c, hc⟩ := split_of_small l a (k + m + K) m fun i =>
    (le_ciSup (f := fun n : ℕ => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) *
      ((l : ℝ)⁻¹) ^ n) ⟨1, by rintro _ ⟨i, rfl⟩; exact term_le_one l a i⟩ i).trans hN
  refine ⟨c, ?_⟩
  have h2 := map_mem_kerP l _ m hc
  rw [show k + m + K - m = k + K by omega, map_sub, ← ha, map_natCast] at h2
  rw [← Ideal.unit_mul_mem_iff_mem _ ((GlobalTheory.RingBasics.isUnit_l l).pow K)]
  convert h2 using 1
  simp only [map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.MemLoc.GaussDefinite

namespace GlobalTheory.MemLoc

theorem gauss_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  intro l hl N hN b hb hb0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  obtain ⟨h01, hadd, hneg, hm, hA⟩ := hN _ le_rfl (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨j, hj⟩ := exists_isCrisP l
  refine hb (crisP_injective l j hj ?_)
  rw [map_zero]
  refine GlobalTheory.RingIface.ev_ext l _ _ fun m => ?_
  rw [map_zero]
  obtain ⟨N₀, hN₀⟩ := hj.bdd m
  obtain ⟨a, ha⟩ := hN₀ b
  have hu : IsUnit (Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N₀)) := by
    have := ((GlobalTheory.RingBasics.isUnit_l l).pow N₀).map (Ideal.Quotient.mk (Per.kerP l ^ m))
    rw [map_pow, map_natCast] at this ⊢
    exact this
  rw [← hu.mul_right_eq_zero, ← map_mul, ha, Ideal.Quotient.eq_zero_iff_mem]
  refine image_kerP_pow_separated l m a fun k => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 b (k + m)
  have hz : N (l : ℝ)⁻¹ (-((l : Per.Acris l) ^ (k + m) * z)) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    rw [hneg, hm, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), ← map_pow, hA]
    exact (mul_le_mul (GaussDefinite.gauss_pow_le l _) (h01 z).2 (h01 z).1 (by positivity)).trans
      (mul_one _).le
  have hs' : N (l : ℝ)⁻¹ (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    have e : algebraMap (Per.Acris0 l) (Per.Acris l) s = b + -((l : Per.Acris l) ^ (k + m) * z) := by
      rw [hs]; ring
    rw [e]
    refine (hadd _ _).trans (max_le ?_ hz)
    rw [hb0]
    positivity
  obtain ⟨c, hc⟩ := GaussDefinite.envelope_split l (N (l : ℝ)⁻¹) (fun x => (h01 x).1) hm hA s k m hs'
  obtain ⟨a', ha'⟩ := hN₀ z
  have hev : Per.ev l m (algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
      Ideal.Quotient.mk _ (s : Per.AinfP l) := GlobalTheory.RingIface.ev_alg l m _
  refine ⟨(l : Per.Ainf l) ^ N₀ * c + (l : Per.Ainf l) ^ m * a', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
  rw [hs] at ha
  simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, hj.on0, hev] at ha ha' hc ⊢
  linear_combination -ha + (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ (k + m) * ha' +
    (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ N₀ * hc

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_norm_of_nonzero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.gauss_ne_zero | exact GlobalTheory.MemLoc.gauss_ne_zero | (intros; apply GlobalTheory.MemLoc.gauss_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenerator
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LineLattice

theorem exists_generator {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T]
    (hsp : Submodule.span LL (T : Set V) = ⊤) (h1 : Module.finrank LL V = 1) :
    ∃ v : V, v ≠ 0 ∧ T = Submodule.span O {v} := by
  classical
  have hfin : Module.Finite LL V := Module.finite_of_finrank_eq_succ h1
  let b := Module.Free.chooseBasis O T
  have hli : LinearIndependent O (fun i => (b i : V)) :=
    b.linearIndependent.map' T.subtype T.ker_subtype
  have hli' : LinearIndependent LL (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing O LL).1 hli
  have hT : T = Submodule.span O (Set.range fun i => (b i : V)) := by
    have h := congrArg (Submodule.map T.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hfi : Finite (Module.Free.ChooseBasisIndex O T) := hli'.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O T)
  have hc := hli'.fintype_card_le_finrank
  rw [h1] at hc
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) :=
    Fintype.card_le_one_iff_subsingleton.1 hc
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O T) with he | ⟨⟨i⟩⟩
  · exfalso
    rw [Set.range_eq_empty, Submodule.span_empty] at hT
    have hb : Submodule.span LL (T : Set V) = ⊥ := by
      rw [hT]; simp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    exact bot_ne_top (hb.symm.trans hsp)
  · refine ⟨b i, hli.ne_zero i, ?_⟩
    refine hT.trans ?_
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j i]; rfl
    · rintro rfl
      exact ⟨i, rfl⟩

theorem lattice_rank_one {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [IsDomain O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (h1 : Module.finrank LL V = 1) :
    (∃ e : LL ≃ₗ[LL] V, ∀ x : LL, e x ∈ L.T ↔ x ∈ Set.range (algebraMap O LL)) ∧
    ∀ a : O, a ≠ 0 →
      Nonempty (↥(Submodule.torsionBy O (V ⧸ L.T) a) ≃ₗ[O] (O ⧸ Ideal.span {a})) := by
  haveI := L.free
  obtain ⟨v, hv, hT⟩ := exists_generator L.T L.span h1
  have hsurj : ∀ w : V, ∃ c : LL, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).1 h1
  have hmem : ∀ x : LL, x • v ∈ L.T ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    rw [hT, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← algebraMap_smul LL c v] at hc
      exact smul_left_injective LL hv hc
    · rintro ⟨c, rfl⟩
      exact ⟨c, (algebraMap_smul LL c v).symm⟩
  refine ⟨⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL V v)
    ⟨smul_left_injective LL hv, hsurj⟩, hmem⟩, ?_⟩
  intro a ha
  have ha' : algebraMap O LL a ≠ 0 := by
    simpa using ha
  have hx : L.T.mkQ ((algebraMap O LL a)⁻¹ • v) ∈ Submodule.torsionBy O (V ⧸ L.T) a := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem,
      mul_inv_cancel₀ ha']
    exact ⟨1, map_one _⟩
  let f : O →ₗ[O] Submodule.torsionBy O (V ⧸ L.T) a :=
    LinearMap.toSpanSingleton O _ ⟨_, hx⟩
  have hf : ∀ c : O, (f c : V ⧸ L.T) =
      L.T.mkQ ((algebraMap O LL c * (algebraMap O LL a)⁻¹) • v) := by
    intro c
    rw [← smul_smul, algebraMap_smul, map_smul]
    rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := L.T.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hsurj w
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [hf, hc, mul_comm (algebraMap O LL a) x, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  have hk : LinearMap.ker f = Ideal.span {a} := by
    ext c
    rw [LinearMap.mem_ker, Subtype.ext_iff, hf, Ideal.mem_span_singleton']
    rw [Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective O LL ?_⟩
      rw [map_mul, hd, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_mul, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  exact ⟨(f.quotKerEquivOfSurjective hfs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end GlobalTheory.LineLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem geom_sum_add_one_eq_sum_choose {R : Type*} [Ring R] (D : R) (n : ℕ) :
    ∑ i ∈ Finset.range n, (D + 1) ^ i = ∑ j ∈ Finset.range n, n.choose (j + 1) • D ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := (Commute.one_right D).add_pow n
    simp only [one_pow, mul_one] at h
    rw [h]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n,
      Nat.choose_succ_self, zero_smul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul, Nat.cast_comm]

theorem norm_geom_sum_galois_le (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) :
    ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧
      ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  intro x hx
  set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM

  have hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih => intro y hy; rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ (ih y hy)

  let T : AddMonoid.End (Om l) := AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)
  have hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]; rfl
  have hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [pow_succ']
      change σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧
        ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖
      refine ⟨S.sub_mem (hS _ h1) h1, ?_⟩
      calc ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s * ‖((T - 1) ^ j) y‖ := hσ _ h1
        _ ≤ s * (s ^ j * ‖y‖) := mul_le_mul_of_nonneg_left h2 hs0
        _ = s ^ (j + 1) * ‖y‖ := by ring

  have hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)

  have key := geom_sum_add_one_eq_sum_choose (T - 1) l
  rw [sub_add_cancel] at key
  have hsum : ∑ i ∈ Finset.range l, (σ ^ i) x =
      ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x := by
    let ev : AddMonoid.End (Om l) →+ Om l :=
      { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_nsmul] at h
    calc ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ i ∈ Finset.range l, (T ^ i) x :=
          Finset.sum_congr rfl fun i _ => (hT i x).symm
      _ = _ := h
  have hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖ := by
    rw [hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_
    obtain ⟨-, hle⟩ := hD j x hx
    have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0 hs1
    rw [nsmul_eq_mul, norm_mul]
    rcases Nat.lt_or_ge (j + 1) l with hlt | hge
    ·
      obtain ⟨m, hm⟩ := (Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt
      rw [hm, Nat.cast_mul, norm_mul]
      have h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))
      calc _ ≤ ‖((l : ℕ) : Om l)‖ * 1 * (1 * ‖x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ ≤ M * ‖x‖ := by
            rw [mul_one, one_mul]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    ·
      have hjl : j = l - 1 := by have := Finset.mem_range.mp hj; omega
      have hc : l.choose (j + 1) = 1 := by
        rw [show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]
      rw [hc, Nat.cast_one, norm_one, one_mul]
      calc _ ≤ s ^ j * ‖x‖ := hle
        _ ≤ M * ‖x‖ := by
            rw [hjl]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

  set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy
  have hyS : y ∈ S := S.sum_mem fun i _ => hpowS i x hx
  have htel : (σ ^ l) x - x = σ y - y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, ← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun i => (σ ^ i) x) l
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  refine ⟨hbound, ?_⟩
  rw [htel]
  calc ‖σ y - y‖ ≤ s * ‖y‖ := hσ y hyS
    _ ≤ s * (M * ‖x‖) := mul_le_mul_of_nonneg_left hbound hs0
    _ = M * s * ‖x‖ := by ring

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end
end

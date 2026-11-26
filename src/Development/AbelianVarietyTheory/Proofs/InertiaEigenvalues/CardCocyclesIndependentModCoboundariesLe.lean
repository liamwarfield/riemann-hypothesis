module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMem
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem condC_sh_and_nab_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hC a
  have h : ∀ x ∈ sh a N, nab g x ∈ sh a N := fun x hx => Window.nab_mem_sh R hg hC a hx
  exact ⟨(condC_iff_nab_mem g _).2 h, h⟩

end GlobalTheory.PhiGam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMemStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaCondition_shift_and_divVariable_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  first | exact @GlobalTheory.PhiGam.condC_sh_and_nab_mem | exact GlobalTheory.PhiGam.condC_sh_and_nab_mem | (intros; apply GlobalTheory.PhiGam.condC_sh_and_nab_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisBis
namespace GlobalTheory.PowerMembershipInertiaEigenvalues

theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add (f := _), LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomial
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.GenKernelFit

theorem aeval_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (p : Polynomial k) : ∀ y ∈ Q, Polynomial.aeval T p y ∈ Q := by
  first
  | exact @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main ..)

theorem apply_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (f : Polynomial k) (hf : f.eval 0 ≠ 0) (x : U)
    (h1 : T (Polynomial.aeval T f x) ∈ Q) (j : ℕ) (h2 : (T ^ j) x ∈ Q) : T x ∈ Q := by
  have hc : IsCoprime f Polynomial.X := by
    refine ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_).symm
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hf
  obtain ⟨a, b, hab⟩ := hc.pow_right (n := j)
  have e : (Polynomial.X : Polynomial k) =
      a * (Polynomial.X * f) + b * (Polynomial.X * Polynomial.X ^ j) := by
    linear_combination (-Polynomial.X) * hab
  have e2 : T x = Polynomial.aeval T a (T (Polynomial.aeval T f x)) + Polynomial.aeval T b (T ((T ^ j) x)) := by
    have := congrArg (fun p => Polynomial.aeval T p x) e
    simpa only [map_add (f := _), map_mul, map_pow, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply]
      using this
  rw [e2]
  exact Q.add_mem (aeval_mem T Q hQ a _ h1) (aeval_mem T Q hQ b _ (hQ _ h2))

theorem nab_mem_of_ePoly : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  intro k _ l n m _ _ _ R D i N s hC hE x hx hj
  obtain ⟨f, hf, hE⟩ := hE
  obtain ⟨j, hj⟩ := hj
  exact apply_mem (nab (D.γ i)) ((sh s N).restrictScalars k)
    (GlobalTheory.PhiGam.condC_sh_and_nab_mem R (D.γ i) (D.γ_semi i) N hC s).2 f hf x (hE x hx) j hj

end GlobalTheory.GenKernelFit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomialStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaNabla_mem_of_killing_polynomial : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  first | exact @GlobalTheory.GenKernelFit.nab_mem_of_ePoly | exact GlobalTheory.GenKernelFit.nab_mem_of_ePoly | (intros; apply GlobalTheory.GenKernelFit.nab_mem_of_ePoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
noncomputable section
namespace GlobalTheory.PhiGam.PolarCount
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem rank_nullity {W : Type} [AddCommGroup W] [Module k W] (A : Submodule k U) [FiniteDimensional k A]
    (f : U →ₗ[k] W) :
    finrank k (A.map f) + finrank k (A ⊓ LinearMap.ker f : Submodule k U) = finrank k A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem count (T : Module.End k U) (F L N Z S S' : Submodule k U) [FiniteDimensional k S]
    [FiniteDimensional k S'] (hLN : L ≤ N) (hNF : N ≤ F) (hTL : L ≤ L.comap T) (hF' : F ≤ S' ⊔ L)
    (hF : F ≤ S ⊔ F.map T ⊔ L) (he : ∀ x ∈ N, (∃ m : ℕ, (T ^ m) x ∈ L) → T x ∈ L)
    (hZ : ∀ x ∈ Z, x ∈ F ∧ T x ∈ L) :
    finrank k (↥Z ⧸ N.submoduleOf Z) + gmult T N L 0 ≤ finrank k S := by
  unfold gmult
  rw [finrank_quot, finrank_quot]
  rw [map_zero (algebraMap k (Module.End k U)), sub_zero]
  set Tb : (U ⧸ L) →ₗ[k] (U ⧸ L) := L.mapQ L T hTL with hTb
  set h : (U ⧸ L) →ₗ[k] (U ⧸ N) := Submodule.factor hLN with hh
  set Fb := F.map L.mkQ with hFb
  have hL0 : L.map L.mkQ = ⊥ := by simp
  have hfin : FiniteDimensional k Fb := by
    have : Fb ≤ S'.map L.mkQ := by
      have := Submodule.map_mono (f := L.mkQ) hF'
      rwa [Submodule.map_sup, hL0, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le this
  set Kb : Submodule k (U ⧸ L) := Fb ⊓ LinearMap.ker Tb with hKb
  have hKfin : FiniteDimensional k Kb := Submodule.finiteDimensional_of_le inf_le_left
  have h1 := rank_nullity Fb Tb
  rw [← hKb] at h1
  have h2 : Fb ≤ S.map L.mkQ ⊔ Fb.map Tb := by
    have := Submodule.map_mono (f := L.mkQ) hF
    rw [Submodule.map_sup, hL0, sup_bot_eq, Submodule.map_sup] at this
    refine this.trans (sup_le_sup_left ?_ _)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨L.mkQ x, ⟨x, hx, rfl⟩, rfl⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank (S.map L.mkQ) (Fb.map Tb)
  have h5 := Submodule.finrank_map_le L.mkQ S
  have h6 := rank_nullity Kb h
  have hmem : ∀ x ∈ F, T x ∈ L → L.mkQ x ∈ Kb := by
    intro x hx hT
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    show L.mkQ (T x) = 0
    simpa using hT
  have h7 : Z.map N.mkQ ≤ Kb.map h := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨L.mkQ x, hmem x (hZ x hx).1 (hZ x hx).2, rfl⟩
  have h8 : (N ⊓ ⨆ m : ℕ, L.comap (T ^ m)).map L.mkQ ≤ Kb ⊓ LinearMap.ker h := by
    rintro _ ⟨x, ⟨hxN, hx⟩, rfl⟩
    refine ⟨hmem x (hNF hxN) (he x hxN ?_), ?_⟩
    · have hmono : Monotone (fun m : ℕ => L.comap (T ^ m)) := by
        refine monotone_nat_of_le_succ fun m y hy => ?_
        show (T ^ (m + 1)) y ∈ L
        rw [pow_succ']
        exact hTL hy
      exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 hx
    · show N.mkQ x = 0
      simpa using hxN
  have h9 := Submodule.finrank_mono h7
  have h10 := Submodule.finrank_mono h8
  omega
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem vv_ne : vv k ≠ 0 := by
  unfold vv; exact HahnSeries.single_ne_zero one_ne_zero

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  unfold vv; simp

theorem coe_smul (b : k⟦X⟧) (x : V) : (b : k⸨X⸩) • x = b • x :=
  algebraMap_smul k⸨X⸩ b x

theorem mem_sh {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} : x ∈ sh a N ↔ ∃ y ∈ N, vv k ^ a • y = x := by
  unfold sh; rw [Submodule.mem_map]; rfl

theorem smul_mem_sh {a : ℤ} (b : ℤ) {N : Submodule k⟦X⟧ V} {x : V} (h : x ∈ sh a N) :
    vv k ^ b • x ∈ sh (a + b) N := by
  obtain ⟨y, hy, rfl⟩ := mem_sh.1 h
  exact mem_sh.2 ⟨y, hy, by rw [smul_smul, ← zpow_add₀ vv_ne, add_comm]⟩

theorem sh_zero (N : Submodule k⟦X⟧ V) : sh 0 N = N := by
  ext x; simp [mem_sh]

theorem sh_sh (a b : ℤ) (N : Submodule k⟦X⟧ V) : sh b (sh a N) = sh (a + b) N := by
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := mem_sh.1 h
    exact smul_mem_sh b hy
  · intro h
    refine mem_sh.2 ⟨vv k ^ (-b) • x, ?_, ?_⟩
    · simpa using smul_mem_sh (-b) h
    · rw [smul_smul, ← zpow_add₀ vv_ne]; simp

theorem sh_mono (a : ℤ) {N P : Submodule k⟦X⟧ V} (h : N ≤ P) : sh a N ≤ sh a P :=
  Submodule.map_mono h

theorem sh_anti {a b : ℤ} (h : a ≤ b) (N : Submodule k⟦X⟧ V) : sh b N ≤ sh a N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sh.1 hx
  obtain ⟨m, rfl⟩ := Int.le.dest h
  refine mem_sh.2 ⟨(PowerSeries.X ^ m : k⟦X⟧) • y, N.smul_mem _ hy, ?_⟩
  rw [← coe_smul, smul_smul, zpow_add₀ vv_ne, zpow_natCast, vv_eq, map_pow]

theorem nab_apply (g : V →ₗ[k] V) (x : V) : nab g x = vv k ^ (-1 : ℤ) • (g x - x) := by
  rw [zpow_neg_one]; rfl

theorem span_le {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V) (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq, coe_smul, mul_smul]

theorem fin_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := span_le e _ he
    rw [sh_sh] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem gens [FiniteDimensional k⸨X⸩ V] (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    ∃ (n : ℕ) (e : Fin n → V), n ≤ finrank k⸨X⸩ V ∧ Submodule.span k⟦X⟧ (Set.range e) = N := by
  have : Module.Finite k⟦X⟧ N := Module.Finite.iff_fg.2 hN
  have : Module.IsTorsionFree k⟦X⟧ V := Module.IsTorsionFree.trans_faithfulSMul k⟦X⟧ k⸨X⸩ V
  have : Module.Free k⟦X⟧ N := inferInstance
  let b := Module.finBasis k⟦X⟧ N
  refine ⟨_, N.subtype ∘ b, ?_, ?_⟩
  · have hli : LinearIndependent k⟦X⟧ (N.subtype ∘ b) := b.linearIndependent.map' _ N.ker_subtype
    have := ((LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).1 hli).fintype_card_le_finrank
    simpa using this
  · rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem phi_sh {l : ℕ} (R : RingPG k l) (f : V →ₗ[k] V) (hf : Semi R.φ f) (N : Submodule k⟦X⟧ V) (t : ℕ)
    {y : V} (hy : y ∈ sh t N) : f y ∈ sh (l * t : ℕ) (pull f N) := by
  obtain ⟨z, hz, rfl⟩ := mem_sh.1 hy
  obtain ⟨u, hu⟩ := R.φ_v
  refine mem_sh.2 ⟨((u : k⟦X⟧) ^ t) • f z, Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩), ?_⟩
  rw [hf, zpow_natCast, zpow_natCast, map_pow, hu, ← coe_smul, smul_smul, map_pow, mul_pow, ← pow_mul, mul_comm]

theorem psi_mem (f ψ : V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩) (h : ∀ (a : k⸨X⸩) x, ψ (a • f x) = ψ0 a • x) (a : ℤ)
    (h0 : ∀ b : k⟦X⟧, ∃ c : k⟦X⟧, (c : k⸨X⸩) = ψ0 (vv k ^ a * (b : k⸨X⸩))) (N : Submodule k⟦X⟧ V)
    {y : V} (hy : y ∈ sh a (pull f N)) : ψ y ∈ N := by
  obtain ⟨z, hz, rfl⟩ := mem_sh.1 hy
  suffices H : ∀ b : k⟦X⟧, ψ (vv k ^ a • b • z) ∈ N by simpa using H 1
  clear hy
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro b
    obtain ⟨c, hc⟩ := h0 b
    rw [← coe_smul, smul_smul, h, ← hc, coe_smul]
    exact N.smul_mem _ hx
  | zero => intro b; simp
  | add x y _ _ hx hy => intro b; rw [smul_add, smul_add, map_add (f := _)]; exact N.add_mem (hx b) (hy b)
  | smul c x _ hx => intro b; rw [smul_smul b c]; exact hx _

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D ψ ψ0 hψ _ hψ1 _ hP i N₀ N ws s w hN₀ hN hC₀ hC hws hl hb ha hd hs
    hPSI he Z hZ
  have hv : vv k ≠ 0 := vv_ne
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R (D.γ i) (D.γ_semi i) N hN hC 0 (ws + 1) 0
  simp only [zero_add, Int.cast_natCast, sh_zero] at hr
  rw [← hr, Nat.cast_succ]
  obtain ⟨r, e, hre, hspan⟩ := gens N₀ hN₀.1
  set M := pull (D.φ i) N₀ with hM
  let A : V →ₗ[k] V := ((vv k ^ (-1 : ℤ) • (LinearMap.id : V →ₗ[k⸨X⸩] V)).restrictScalars k) ∘ₗ D.φ i
  have hA : ∀ x, A x = vv k ^ (-1 : ℤ) • D.φ i x := fun _ => rfl
  have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range e)
  have hS : finrank k ((Submodule.span k (Set.range e)).map A) ≤ finrank k⸨X⸩ V := by
    refine (Submodule.finrank_map_le _ _).trans (le_trans ?_ hre)
    exact (finrank_range_le_card (R := k) e).trans (by simp)
  obtain ⟨S', hS', hF'⟩ := fin_quot N hN.1 (min (-w + -ws) (ws + 1)) (ws + 1 - min (-w + -ws) (ws + 1)).toNat
  rw [Int.toNat_of_nonneg (by omega), add_sub_cancel] at hF'
  have hNF : N ≤ sh (-ws) M := by
    have := sh_mono (-ws) hb
    rwa [sh_sh, add_neg_cancel, sh_zero] at this
  have hMF : M ≤ sh (-ws) M := by
    have := sh_anti (show (-ws : ℤ) ≤ 0 by omega) M
    rwa [sh_zero] at this
  refine le_trans (count (nab (D.γ i)) ((sh (-ws) M).restrictScalars k) ((sh (ws + 1) N).restrictScalars k)
    (N.restrictScalars k) Z ((Submodule.span k (Set.range e)).map A) S' ?_ hNF ?_ ?_ ?_ he ?_) hS
  · have := sh_anti (show (0 : ℤ) ≤ ws + 1 by omega) N
    rwa [sh_zero] at this
  · intro x hx
    exact (GlobalTheory.T.gammaCondition_shift_and_divVariable_mem R (D.γ i) (D.γ_semi i) N hC (ws + 1)).2 x hx
  · refine le_trans ?_ hF'
    intro x hx
    have := sh_mono (-ws) ha hx
    rw [sh_sh] at this
    exact sh_anti (min_le_left _ _) N this
  · intro x hx
    have h1 : vv k ^ (1 : ℤ) • x ∈ sh (1 - ws) M := by
      have := smul_mem_sh 1 hx
      rwa [neg_add_eq_sub] at this
    have hy : ψ i (vv k ^ (1 : ℤ) • x) ∈ N₀ := by
      refine psi_mem (D.φ i) (ψ i) ψ0 (hψ i) (1 - ws) (fun b => ?_) N₀ h1
      have : ψ0 (vv k ^ (1 - ws : ℤ) * (b : k⸨X⸩)) ∈ Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩)) := by
        rw [← hP (1 - ws) (by omega) (by omega)]
        exact ⟨_, ⟨b, rfl⟩, rfl⟩
      exact this
    set y := ψ i (vv k ^ (1 : ℤ) • x) with hydef
    have hφM : ∀ z ∈ N₀, D.φ i z ∈ M := fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩
    have hM1 : M ≤ sh (1 - ws) M := by
      have := sh_anti (show (1 - ws : ℤ) ≤ 0 by omega) M
      rwa [sh_zero] at this
    obtain ⟨x', hx', -, hx'e⟩ := hPSI (vv k ^ (1 : ℤ) • x - D.φ i y) (Submodule.sub_mem _ h1 (hM1 (hφM y hy)))
      (by
        have := hψ i 1 y
        rw [one_smul, hψ1, one_smul] at this
        rw [map_sub, this, sub_self])
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Submodule.mem_sup.1 (span_le e N₀ hspan hy)
    obtain ⟨y3, hy3, rfl⟩ := mem_sh.1 hy2
    obtain ⟨z, hz, hz'⟩ := (GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ (i - 1)) (D.γ_semi _) N₀ hN₀ hC₀ 0 (s + 2) (fun j hj => by
      simpa using hs j (by omega))).2 y3 (by rwa [sh_zero])
    rw [sh_zero] at hz
    have hz2 : vv k ^ (1 : ℤ) • (y3 - nab (D.γ (i - 1)) z) ∈ sh ((s + 3 : ℕ) : ℤ) N₀ := by
      have := smul_mem_sh 1 hz'
      convert this using 2
      push_cast; ring
    have hz3 := smul_mem_sh (-1) (sh_mono _ ha (phi_sh R (D.φ i) (D.φ_semi i) N₀ _ hz2))
    rw [sh_sh] at hz3
    have hz4 := sh_anti (a := (ws : ℤ) + 1) (by push_cast; omega) N hz3
    have hvv : ∀ u : V, vv k ^ (1 : ℤ) • vv k ^ (-1 : ℤ) • u = u := fun u => by
      rw [smul_smul, ← zpow_add₀ hv]; simp
    have hvv' : ∀ u : V, vv k ^ (-1 : ℤ) • vv k ^ (1 : ℤ) • u = u := fun u => by
      rw [smul_smul, ← zpow_add₀ hv]; simp
    have key : x = A y1 + nab (D.γ i) (x' + D.φ i z) +
        vv k ^ (-1 : ℤ) • D.φ i (vv k ^ (1 : ℤ) • (y3 - nab (D.γ (i - 1)) z)) := by
      rw [hA, map_add (f := _), nab_apply, nab_apply, nab_apply, hx'e, ← hy12, smul_sub (vv k ^ (1 : ℤ)), hvv,
        ← D.comm, map_sub, map_sub, map_add, ← smul_add, ← smul_add, ← smul_add]
      rw [← hvv' x, hvv]
      congr 1
      abel
    rw [key]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup ⟨y1, hy1, rfl⟩
      ⟨x' + D.φ i z, Submodule.add_mem _ hx' (hMF (hφM z hz)), rfl⟩) hz4
  · intro x hx
    refine ⟨(hZ x hx).1, ?_⟩
    have := smul_mem_sh (-1) (hZ x hx).2
    rw [nab_apply]
    show _ ∈ sh (ws + 1) N
    convert this using 2
    ring

end GlobalTheory.PhiGam.PolarCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRankStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  first | exact @GlobalTheory.PhiGam.PolarCount.main | exact GlobalTheory.PhiGam.PolarCount.main | (intros; apply GlobalTheory.PhiGam.PolarCount.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeights
noncomputable section
namespace GlobalTheory.PhiGam.PolarKernel
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem finrank_le_gmult (T : Module.End k U) (P Q Z S : Submodule k U) [FiniteDimensional k S]
    (hP : P ≤ S ⊔ Q) (hZ : ∀ x ∈ Z, x ∈ P ∧ T x ∈ Q) :
    finrank k (↥Z ⧸ Q.submoduleOf Z) ≤ gmult T P Q 0 := by
  unfold gmult
  rw [finrank_quot, finrank_quot, map_zero (algebraMap k (Module.End k U)), sub_zero]
  have hfin : FiniteDimensional k ((P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ) := by
    have h : (P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ ≤ S.map Q.mkQ := by
      have := Submodule.map_mono (f := Q.mkQ) ((inf_le_left (b := ⨆ m : ℕ, Q.comap (T ^ m))).trans hP)
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le h
  refine Submodule.finrank_mono (Submodule.map_mono fun x hx => ⟨(hZ x hx).1, ?_⟩)
  refine Submodule.mem_iSup_of_mem 1 ?_
  rw [Submodule.mem_comap, pow_one]
  exact (hZ x hx).2
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem le_span_sup {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V)
    (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh_iff_exists.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq_coe_X, mul_smul]
  exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) _

theorem exists_finite_le_sup (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := le_span_sup e _ he
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC w Z hZ
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R g hg N hN hC (-w) w 0
  simp only [zero_add, neg_add_cancel, sh_zero_eq] at hr
  obtain ⟨S, hS, hF⟩ := exists_finite_le_sup N hN.1 (-w) w
  rw [neg_add_cancel, sh_zero_eq] at hF
  rw [← hr]
  exact finrank_le_gmult (nab g) _ _ Z S hF hZ

end GlobalTheory.PhiGam.PolarKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  first | exact @GlobalTheory.PhiGam.PolarKernel.main | exact GlobalTheory.PhiGam.PolarKernel.main | (intros; apply GlobalTheory.PhiGam.PolarKernel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeSmulMem
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Gauge
section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem _root_.GlobalTheory.PhiGam.Gauge.phi_sh {l : ℕ} (R : _root_.GlobalTheory.PhiGam.RingPG k l)
    (f : V →ₗ[k] V) (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (N N' : Submodule k⟦X⟧ V) (w : ℤ)
    (h : _root_.GlobalTheory.PhiGam.pull f N' ≤ _root_.GlobalTheory.PhiGam.sh (-w) N) (m : ℕ) {x : V}
    (hx : x ∈ _root_.GlobalTheory.PhiGam.sh m N') :
    f x ∈ _root_.GlobalTheory.PhiGam.sh (l * m - w) N := by
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := R.φ_v
  have hfy : f y ∈ _root_.GlobalTheory.PhiGam.sh (-w) N := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hfy
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_exists]
  refine ⟨((u : k⟦X⟧) ^ m) • z, N.smul_mem _ hz, ?_⟩
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [zpow_natCast, hf, map_pow, hu, ← hz', ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) ^ m) z, smul_smul,
    smul_smul, LaurentSeries.coe_algebraMap, map_pow, sub_eq_add_neg, zpow_add₀ hX, mul_pow, ← pow_mul]
  congr 1
  rw [show ((l : ℤ) * (m : ℤ)) = ((l * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

end

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem vv_smul_mem_sh_succ_iff (a : ℤ) (N : Submodule k⟦X⟧ V) (y : V) :
    _root_.GlobalTheory.PhiGam.vv k • y ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) N ↔
      y ∈ _root_.GlobalTheory.PhiGam.sh a N := by
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, _root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, smul_smul, ← zpow_add_one₀ hX]
  rw [show -(a + 1) + 1 = -a by ring]

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem apply_sub_self_eq_vv_smul_nab (f : V →ₗ[k] V) (x : V) :
    f x - x = _root_.GlobalTheory.PhiGam.vv k • _root_.GlobalTheory.PhiGam.nab f x := by
  rw [_root_.GlobalTheory.PhiGam.nab_apply_eq, smul_smul, mul_inv_cancel₀ (_root_.GlobalTheory.PhiGam.vv_ne_zero k),
    one_smul]

theorem _root_.GlobalTheory.PhiGam.Gauge.main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l]
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V] (D : _root_.GlobalTheory.PhiGam.ModPG R n V), ∀ (w w' : ZMod n → ℤ) (s : ZMod n → ℕ)
    (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, _root_.GlobalTheory.PhiGam.IsLat (N i)) →
    _root_.GlobalTheory.PhiGam.CondAB D.φ w w' N →
    (∀ i, _root_.GlobalTheory.PhiGam.CondC (D.γ i) (N i)) →
    (∀ i, (s i : ℤ) + 1 ≤ l * (s (i - 1) + 1) - w i) →
    (∀ i (a : ℕ), a ≤ s i + 1 → _root_.GlobalTheory.PhiGam.sen (D.γ i) (N i) (a : k) = 0) →
    ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i =
      D.φ i (g (i - 1)) - g i) →
    (∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh 1 (N i)) →
    (∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧
      ∀ i, g i - (D.γ i (m i) - m i) ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) ∧
    ((∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) → (∀ i, b i ∈ N i) →
      ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧
        g i = D.γ i (m i) - m i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D w w' s N hN hAB hC hs hsen b g hcoc hg
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hW : ∀ i, _ := fun i => _root_.GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ i)
    (D.γ_semi i) (N i) (hN i) (hC i) 0 (s i + 2) (fun j hj => by
      simpa using hsen i j (by omega))
  refine ⟨?_, fun hg3 hb => ?_⟩
  · have key : ∀ i, ∃ x ∈ N i, g i - (D.γ i x - x) ∈
        _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i) := by
      intro i
      have hy : (_root_.GlobalTheory.PhiGam.vv k)⁻¹ • g i ∈ _root_.GlobalTheory.PhiGam.sh 0 (N i) := by
        rw [← vv_smul_mem_sh_succ_iff, smul_inv_smul₀ hX]
        simpa using hg i
      obtain ⟨x, hx, hxy⟩ := (hW i).2 _ hy
      refine ⟨x, by rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at hx, ?_⟩
      have h3 := (vv_smul_mem_sh_succ_iff _ _ _).2 hxy
      rw [smul_sub, smul_inv_smul₀ hX, ← apply_sub_self_eq_vv_smul_nab] at h3
      convert h3 using 2
      push_cast
      ring
    choose m hm1 hm2 using key
    exact ⟨m, hm1, hm2⟩
  · set φ := D.φ
    set γ := D.γ
    have hφ : ∀ i (a : ℕ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N (i - 1)) →
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh (l * a - w i) (N i) := fun i a x hx =>
      _root_.GlobalTheory.PhiGam.Gauge.phi_sh R (φ i) (D.φ_semi i) (N i)
        (N (i - 1)) (w i) (hAB i).1 a hx
    have hγ : ∀ i (a : ℤ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N i) →
        γ i x - x ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) (N i) := fun i a x hx => by
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff]
      exact _root_.GlobalTheory.PhiGam.Window.nab_mem_sh R (D.γ_semi i) (hC i) a hx
    have hb' : ∀ i, b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i) := by
      intro i
      have h1 : γ i (b i) - b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2 + 1) (N i) := by
        rw [hcoc i]
        refine sub_mem ?_ (by convert hg3 i using 2; ring)
        have h2 := hφ i (s (i - 1) + 3) (by push_cast; exact hg3 (i - 1))
        refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ h2
        have := hs i
        push_cast
        nlinarith
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff] at h1
      have := (hW i).1 (b i) (by rw [_root_.GlobalTheory.PhiGam.sh_zero_eq]; exact hb i) (by convert h1 using 2; push_cast; ring)
      convert this using 2
      push_cast
      ring
    have hP : ∀ i, ∀ x ∈ _root_.GlobalTheory.PhiGam.sh ((s (i - 1) : ℤ) + 2) (N (i - 1)),
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh 1
          (_root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) := by
      intro i x hx
      rw [_root_.GlobalTheory.PhiGam.sh_sh_eq]
      refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ (hφ i (s (i - 1) + 2) (by push_cast; exact hx))
      have := hs i
      push_cast
      nlinarith
    have hF := _root_.GlobalTheory.PhiGam.one_sub_frob_bij R D
      (fun i => _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) (fun i => (hN i).shift _) hP
    obtain ⟨m, hmP, hmb⟩ := hF.1 b hb'
    change ∀ i, φ i (m (i - 1)) - m i = b i at hmb
    have hg0 := hF.2 (fun i => g i - (γ i (m i) - m i))
      (fun i => sub_mem (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hg3 i))
        (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hγ i _ (hmP i))))
      (fun i => by
        show φ i (g (i - 1) - (γ (i - 1) (m (i - 1)) - m (i - 1))) = g i - (γ i (m i) - m i)
        have e := hcoc i
        rw [← hmb i, map_sub] at e
        have e2 := sub_eq_iff_eq_add.1 e.symm
        have hcomm : ∀ x, φ i (γ (i - 1) x) = γ i (φ i x) := D.comm i
        simp only [map_sub, hcomm]
        rw [e2]
        abel)
    refine ⟨m, fun i => ?_, fun i => ⟨(hmb i).symm, ?_⟩⟩
    · have := _root_.GlobalTheory.PhiGam.sh_le_sh_of_le (show (0 : ℤ) ≤ (s i : ℤ) + 2 by positivity) _ (hmP i)
      rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at this
    · exact sub_eq_zero.1 (congrFun hg0 i)

end GlobalTheory.PhiGam.Gauge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLe
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.PolarBound

theorem card_le_sum {k V ι : Type} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] {s : ℕ}
    (c : ι → Fin s → V) (N : ι → Submodule k V) (d : ι → ℕ)
    (hd : ∀ i, Module.finrank k (↥(LinearMap.range (Fintype.linearCombination k (c i))) ⧸
      (N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))) ≤ d i)
    (hinj : ∀ t : Fin s → k, (∀ i, ∑ a, t a • c i a ∈ N i) → t = 0) : s ≤ ∑ i, d i := by
  let f := LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ
    (Fintype.linearCombination k (c i)).rangeRestrict
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    refine hinj t fun i => ?_
    have h1 : f t i = 0 := congrFun ht i
    exact (Submodule.Quotient.mk_eq_zero ((N i).submoduleOf
      (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h2
  exact h2.trans (Finset.sum_le_sum fun i _ => hd i)

variable {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem cob_mem (D : ModPG R n (Vc k m)) (y : ZMod n → Vc k m) :
    ((fun i => D.φ i (y (i - 1)) - y i, fun i => D.γ i (y i) - y i) :
      (ZMod n → Vc k m) × (ZMod n → Vc k m)) ∈ herrB D := ⟨y, rfl⟩

theorem gauge_one (D : ModPG R n (Vc k m)) (Dt : TopData n m) (N : Lats k n m)
    (hI : ∀ i, (Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i)
    (hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i) (hN : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i (a : ℕ), a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0)
    (z : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : InZZ D Dt N z.1 z.2) :
    ∃ (z' : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (c : ZMod n → Vc k m), z - z' ∈ herrB D ∧
      ∀ i, D.γ i (z'.1 i) - z'.1 i = D.φ i (z'.2 (i - 1)) - z'.2 i ∧ z'.2 i ∈ sh (Dt.sg l i + 3) (N i) ∧
        c i - z'.1 i ∈ N i ∧
        (Dt.ty i = LType.G → c i ∈ sh (-Dt.w i) (N i) ∧ D.γ i (c i) - c i ∈ sh 1 (N i)) ∧
        (Dt.ty i = LType.Bd → c i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
          D.γ i (c i) - c i ∈ sh (Dt.wst i + 2) (N i)) := by
  obtain ⟨b, g⟩ := z
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  obtain ⟨y, hy, hy'⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
    (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g
    (fun i => (hz i).1) (fun i => (hz i).2.1)).1
  have hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧
      (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i)) := by
    intro i
    cases h : Dt.ty i with
    | G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩
    | Bd =>
      obtain ⟨x, hx, hx'⟩ := ((hz i).2.2.2 h).2
      exact ⟨x, hx, fun h => (by cases h), fun _ => hx'⟩
  choose x hx hxG hxB using hx
  refine ⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)),
    fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩
  · convert cob_mem D y using 1
    ext i : 2 <;> simp
  have h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i := (hz i).1
  have hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hy _, rfl⟩
  have hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i) := by
    have h1 := Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3)
      (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))
    refine sh_le_sh_of_le ?_ _ h1
    have := hI i
    unfold TopData.wst
    push_cast; nlinarith
  have hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) =
      D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i)) := by
    simp only [map_sub, map_add (f := _), D.comm]
    linear_combination (norm := module) h0
  have hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    simpa [sh_zero_eq] using sh_le_sh_of_le (a := 0) (b := -a) (by omega) P
  refine ⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp only [map_sub, D.comm]
    linear_combination (norm := module) h0
  · convert (N i).sub_mem (hx i) (hy i) using 1
    simp only []
    abel
  · exact Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))
  · beta_reduce
    rw [hc, hxG i h]
    refine Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))
    · have := (hw i).2; omega
    · omega
  · refine Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_
    have := sh_le_sh (-Dt.wst i) (hAB i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
  · beta_reduce
    rw [hc]
    exact Submodule.sub_mem _ hdeep (hxB i h)

omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem span_prop {s : ℕ} (c : Fin s → Vc k m) (g : Vc k m →ₗ[k] Vc k m) (P Q : Submodule k⟦X⟧ (Vc k m))
    (h : ∀ a, c a ∈ P ∧ g (c a) - c a ∈ Q) :
    ∀ x ∈ LinearMap.range (Fintype.linearCombination k c), x ∈ P ∧ g x - x ∈ Q := by
  rintro _ ⟨t, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]
  refine ⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1,
    Submodule.sum_mem _ fun a _ => ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ _ (h a).2

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli
  have hW := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3
  have hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i := fun i => by
    have h1 := Dt.one_le_letterBlockLength
    have := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
    unfold TopData.wst
    omega
  choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl5 : 5 ≤ l := by have := T1 0; omega
  obtain ⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩ := hΨ.modPG l k hl5 R ι hι
  choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i
  refine card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)
  · cases h : Dt.ty i with
    | G =>
      have e : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (hw i).1
      have := GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by
          have := span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx
          rw [e]
          refine ⟨this.1, ?_⟩
          have h2 := mem_sh_iff_smul_mem.1 this.2
          rwa [zpow_neg_one] at h2)
      rw [e, (hs i).2.1 h] at this
      exact this
    | Bd =>
      have e : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (hw i).2
      obtain ⟨-, -, w1, w2⟩ := (hW i).2.2.2 h
      have h1 := Dt.one_le_letterBlockLength
      have h2 := T1 i
      have h3 := (hW i).1
      obtain ⟨s1, s2⟩ := (hs i).2.2 h
      have := GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2
        (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat
        (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [e]; exact (hAB i).2)
        (hAB i).1 (by rw [e]; unfold TopData.wst; nlinarith) (hs _).1
        (fun y hy hy0 => by
          rw [e] at hy ⊢
          have h4 := (hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)
          have h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1) :=
            ⟨by rwa [neg_add_eq_sub], hy0⟩
          rw [← h4] at h5
          obtain ⟨x, ⟨hx, hx0⟩, hxy⟩ := h5
          exact ⟨x, hx, hx0, hxy⟩)
        (by rw [e]; exact GlobalTheory.T.gammaNabla_mem_of_killing_polynomial D i (N i) _ (hC i) s2)
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by
          rw [e]; exact span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))
      rw [Module.finrank_fin_fun] at this
      omega
  · have hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i) := fun i => by
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1
    obtain ⟨y, -, hy⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
      (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1)
      (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
          map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        exact Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])
      (fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by
        have h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1
        have h2 : ∑ a, t a • c a i ∈ N i := ht i
        convert (N i).sub_mem h2 h1 using 1
        simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib,
          ← smul_sub, sub_sub_cancel])
    have h1 : ∑ a, t a • z' a ∈ herrB D := by
      convert cob_mem D y using 1
      exact Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)
    have h2 : ∑ a, t a • (z a - z' a) ∈ herrB D :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)
    have h3 : ∑ a, t a • z a ∈ herrB D := by
      convert (herrB D).add_mem h1 h2 using 1
      simp only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]
    funext a
    refine Fintype.linearIndependent_iff.1 hli t ?_ a
    have h4 : (herrB D).mkQ (∑ a, t a • z a) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h3
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul] using h4

end GlobalTheory.Models.PolarBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLeStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  first | exact @GlobalTheory.Models.PolarBound.main | exact GlobalTheory.Models.PolarBound.main | (intros; apply GlobalTheory.Models.PolarBound.main <;> assumption)
end

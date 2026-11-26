module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.InvDescent

theorem exists_invariant_of_subgroup {G F Ω V : Type} [Group G] [Field F] [Field Ω]
    [AddCommGroup V] [Module Ω V] (H : Subgroup G) [Finite (G ⧸ H)]
    (ι : F →* Ω) (σ : G → Ω →* Ω) (hσ : ∀ g h c, σ (g * h) c = σ g (σ h c))
    (hσ1 : ∀ c, σ 1 c = c)
    (hH : ∀ g, g ∈ H ↔ ∀ c, σ g (ι c) = ι c)
    (A : G → V →+ V) (hA : ∀ g h v, A (g * h) v = A g (A h v))
    (hAs : ∀ g (c : Ω) v, A g (c • v) = σ g c • A g v)
    (N₀ N₁ : Submodule Ω V) (hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀)
    (y : V) (hy : ∀ h ∈ H, A h y = y) (h0 : y ∈ N₀) (h1 : y ∉ N₁) :
    ∃ z, (∀ g, A g z = z) ∧ z ∈ N₀ ∧ z ∉ N₁ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _

  have key : ∀ (v : V), (∀ h ∈ H, A h v = v) → ∀ g g' : G,
      (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g' → A g v = A g' v := by
    intro v hv g g' hgg'
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hgg', by group⟩
    rw [hA, hv h hh]
  have hfix : ∀ c : F, ∀ h ∈ H, A h (ι c • y) = ι c • y := by
    intro c h hh
    rw [hAs, hy h hh, ((hH h).mp hh) c]

  let T : F → V := fun c => ∑ q : G ⧸ H, A q.out (ι c • y)
  have hTinv : ∀ c g, A g (T c) = T c := by
    intro c g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, ← hA]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun q => ?_)
    apply key _ (hfix c)
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hT0 : ∀ c, T c ∈ N₀ := by
    intro c
    refine Submodule.sum_mem _ (fun q _ => ?_)
    rw [hAs]
    exact N₀.smul_mem _ (hN _ _ h0)
  by_contra hcon
  push Not at hcon
  have hT1 : ∀ c, T c ∈ N₁ := fun c => hcon (T c) (hTinv c) (hT0 c)

  let χ : G ⧸ H → (F →* Ω) := fun q => (σ q.out).comp ι
  have hσinv : ∀ g x, σ g⁻¹ (σ g x) = x := by
    intro g x
    rw [← hσ, inv_mul_cancel, hσ1]
  have hχ : Function.Injective χ := by
    intro q q' hqq'
    have hcq : ∀ c : F, σ q.out (ι c) = σ q'.out (ι c) := fun c => DFunLike.congr_fun hqq' c
    have hmem : q.out⁻¹ * q'.out ∈ H := by
      rw [hH]
      intro c
      rw [hσ, ← hcq, hσinv]
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr hmem
  have hli : LinearIndependent Ω (fun q => (χ q : F → Ω)) :=
    (linearIndependent_monoidHom F Ω).comp χ hχ

  let w : G ⧸ H → V ⧸ N₁ := fun q => N₁.mkQ (A q.out y)
  have hrel : ∀ c : F, ∑ q, χ q c • w q = 0 := by
    intro c
    have hz := (Submodule.Quotient.mk_eq_zero N₁).mpr (hT1 c)
    simp only [T, hAs] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sum] at hz
    simpa [χ, w] using hz
  have hw : ∀ q, w q = 0 := by
    intro q
    rw [← Module.forall_dual_apply_eq_zero_iff Ω]
    intro φ
    have hsum : ∑ q', φ (w q') • (χ q' : F → Ω) = 0 := by
      funext c
      have hcq := congrArg φ (hrel c)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hcq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcq]
      exact Finset.sum_congr rfl (fun q' _ => mul_comm _ _)
    exact Fintype.linearIndependent_iff.mp hli _ hsum q
  have hy1 : A (QuotientGroup.mk (1 : G) : G ⧸ H).out y = y := by
    rw [key y hy _ 1 (QuotientGroup.out_eq' _)]
    exact hy 1 H.one_mem
  have hw1 := hw (QuotientGroup.mk 1)
  simp only [w, Submodule.mkQ_apply, hy1, Submodule.Quotient.mk_eq_zero] at hw1
  exact h1 hw1

variable {l : ℕ} [Fact l.Prime]

theorem smul_mem_Fil (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {x : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil a) : c • x ∈ (P.PD K).Fil a := by

  have hint : IsIntegral ℚ_[l] c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  obtain ⟨K', hcK⟩ : ∃ K' : FinExt l, c ∈ K'.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {c}, IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] c⟩
  have hx' : x ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, ← P.PD_Fil K K' a]
    exact hx
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]
  exact ((P.PD K').Fil a).smul_mem (⟨c, hcK⟩ : K'.1) hx'

noncomputable def filOm (P : LocPrime l) (K : FinExt l) (a : ℤ) : Submodule (Om l) P.R.BdR where
  carrier := ((P.PD K).Fil a : Set P.R.BdR)
  zero_mem' := ((P.PD K).Fil a).zero_mem
  add_mem' := fun h h' => ((P.PD K).Fil a).add_mem h h'
  smul_mem' := fun c _ hx => smul_mem_Fil P K a c hx

theorem finite_quot (K E : FinExt l) : Finite (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) := by
  classical
  have : FiniteDimensional ℚ_[l] E.1 := E.2

  let f : (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) → (E.1 →ₐ[ℚ_[l]] Om l) :=
    fun q => ((q.out : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp E.1.val
  refine Finite.of_injective f (fun q q' hqq' => ?_)
  have hres : ∀ x : E.1, (q.out : GQ l) x = (q'.out : GQ l) x := fun x => DFunLike.congr_fun hqq' x
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ ∈ IntermediateField.fixingSubgroup E.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' := hres ⟨x, hx⟩
  simp only at hx'
  rw [AlgEquiv.mul_apply, ← hx']
  exact AlgEquiv.symm_apply_apply _ _

theorem jump_descends (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l) (_hKE : K.1 ≤ E.1)
    (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l])
    (hM : ∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) (a : ℤ) (y : Fin d → P.R.BdR)
    (hy : ∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (y i)) = y)
    (h0 : ∀ i, y i ∈ (P.PD K).Fil a) (h1 : ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1))) :
    ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧
      ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  have := finite_quot K E
  let am := algebraMap ℚ_[l] P.R.BdR

  let A : ↥(GK K) → (Fin d → P.R.BdR) →+ (Fin d → P.R.BdR) := fun g =>
    AddMonoidHom.mk' (fun v => ((M g).map am).mulVec (fun i => P.actQdR g (v i)))
      (fun v w => by simp only [Pi.add_apply, map_add (f := _)]; exact Matrix.mulVec_add _ _ _)
  have hAapp : ∀ g v, A g v = ((M g).map am).mulVec (fun i => P.actQdR g (v i)) := fun _ _ => rfl
  let σ : ↥(GK K) → Om l →* Om l := fun g => MonoidHom.ofClass (g : GQ l)
  let ι : ↥E.1 →* Om l := MonoidHom.ofClass E.1.val
  have hσ : ∀ g h c, σ (g * h) c = σ g (σ h c) := fun g h c => by
    simp only [σ, MonoidHom.coe_ofClass, Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hσ1 : ∀ c, σ 1 c = c := fun c => by
    simp only [σ, MonoidHom.coe_ofClass, OneMemClass.coe_one, AlgEquiv.one_apply]
  have hH : ∀ g, g ∈ (GK E).subgroupOf (GK K) ↔ ∀ c, σ g (ι c) = ι c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    unfold GK
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h c => h c c.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcomm : ∀ (f : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) (N : Matrix (Fin d) (Fin d) ℚ_[l])
      (w : Fin d → P.R.BdR), (fun i => f ((N.map am).mulVec w i)) = (N.map am).mulVec (fun i => f (w i)) := by
    intro f N w
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, am, AlgEquiv.commutes]
  have hA : ∀ g h v, A (g * h) v = A g (A h v) := by
    intro g h v
    rw [hAapp, hAapp, hAapp, hcomm, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← hM g g.2 h h.2, Subgroup.coe_mul]
    congr 1
    funext i
    rw [map_mul, AlgEquiv.mul_apply]
  have hAs : ∀ g (c : Om l) v, A g (c • v) = σ g c • A g v := by
    intro g c v
    rw [hAapp, hAapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Algebra.smul_def,
      map_mul, P.actQdR_Om, Finset.mul_sum, σ, MonoidHom.coe_ofClass]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  let N₀ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K a)
  let N₁ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K (a + 1))
  have hmem : ∀ (b : ℤ) (v : Fin d → P.R.BdR),
      v ∈ Submodule.pi Set.univ (fun _ => filOm P K b) ↔ ∀ i, v i ∈ (P.PD K).Fil b := by
    intro b v
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀ := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro i
    rw [hAapp]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hj : P.actQdR g (v j) ∈ (P.PD K).Fil a := by
      rw [← P.PD_actdR K g]
      exact (P.PD K).Fil_G g a _ (hv j)
    rw [Matrix.map_apply, ← Algebra.smul_def]
    exact Submodule.smul_of_tower_mem _ _ hj
  obtain ⟨z, hzA, hz0, hz1⟩ := exists_invariant_of_subgroup ((GK E).subgroupOf (GK K)) ι σ hσ hσ1 hH
    A hA hAs N₀ N₁ hN y (fun h hh => hy h ((Subgroup.mem_subgroupOf).mp hh)) ((hmem a y).mpr h0)
    (fun h => h1 ((hmem (a + 1) y).mp h))
  exact ⟨z, fun g hg => hzA ⟨g, hg⟩, (hmem a z).mp hz0, fun h => hz1 ((hmem (a + 1) z).mpr h)⟩

end GlobalTheory.InvDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExtStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  first | exact @GlobalTheory.InvDescent.jump_descends | exact GlobalTheory.InvDescent.jump_descends | (intros; apply GlobalTheory.InvDescent.jump_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltrationStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatrices
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  have hsm : ∀ (c : R) (v : V), c • v = algebraMap R F c • v := fun _ _ => rfl
  haveI : IsScalarTower R F V := ⟨fun c a v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let f' : N →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) f' :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        have : ⇑(algebraMap R (Module.End R V) s) = fun v => algebraMap R F s • v := by
          ext v; rfl
        rw [this]
        exact (MulAction.toPerm (Units.mk0 _ h0) : Equiv.Perm V).bijective
      surj := fun v => by
        obtain ⟨c, hc, x, hx⟩ := hfull v
        exact ⟨(x, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hx⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b.ofIsLocalizedModule F (nonZeroDivisors R) f',
    fun j => b.ofIsLocalizedModule_apply F _ f' j,
    fun x i => b.ofIsLocalizedModule_repr_apply F _ f' x i⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)


include hφ in
omit [IsDomain R] in
theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]


include hφ hint in
theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3


include hφ hint in
theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatricesStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  first | exact @GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | exact GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat | (intros; apply GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKs
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HTBasisEx

variable {l : ℕ} [Fact l.Prime]

theorem basis_of_invariants (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hE : E.1 = Ks K s) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]) (D : Submodule ↥E.1 (Fin d → P.R.BdR))
    (hD : ∀ y ∈ D, ∀ g ∈ GK E,
      ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y)
    (hfin : Module.Finite ↥E.1 ↥D) (hd : Module.finrank ↥E.1 ↥D = d) :
    ∃ (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ), LinearIndependent (PadicComplex l) e ∧
      (∀ k, ∃ y ∈ D, (∀ i, y i ∈ (P.PD E).Fil (u k)) ∧ ¬ ∀ i, y i ∈ (P.PD E).Fil (u k + 1)) ∧
      ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
        (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (e k) = e k := by
  classical
  obtain ⟨sy, hsy⟩ := GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist l P AI Θ E
  have hsum : ∀ (a : ℤ) (t : Finset (Fin d)) (f : Fin d → P.R.BdR),
      (∀ j ∈ t, f j ∈ (P.PD E).Fil a) → sy a (∑ j ∈ t, f j) = ∑ j ∈ t, sy a (f j) := by
    intro a t f
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
    | insert j t hj ih =>
      intro hf
      have ht : ∀ j ∈ t, f j ∈ (P.PD E).Fil a := fun j h => hf j (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        (hsy a).1 _ (hf j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ ht), ih ht]
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.T.exists_family_adapted_to_separated_filtration ↥E.1 (Fin d → P.R.BdR) D
    (fun a => Submodule.pi Set.univ fun _ => (P.PD E).Fil a) d hfin hd
    (fun a y hy i hi => (P.PD E).Fil_anti a (hy i hi))
    (by
      intro y
      choose n hn using fun i => (P.PD E).Fil_exh (y i)
      have hanti : Antitone (P.PD E).Fil := antitone_int_of_succ_le (P.PD E).Fil_anti
      obtain ⟨b, hb⟩ := (Set.finite_range n).bddBelow
      exact ⟨b, fun i _ => hanti (hb ⟨i, rfl⟩) (hn i)⟩)
    (fun y hy => funext fun i => (P.PD E).Fil_sep _ fun a => hy a i (Set.mem_univ i))
  have hxF : ∀ k i, x k i ∈ (P.PD E).Fil (u k) := fun k i => (hx k).2 i (Set.mem_univ i)
  have hact : ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
      (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (fun i => sy (u k) (x k i)) =
        fun i => sy (u k) (x k i) := by
    intro σ hσ k
    funext i
    have hg : ∀ j, P.actQdR σ (x k j) ∈ (P.PD E).Fil (u k) := fun j => by
      rw [← P.PD_actdR E ⟨σ, hσ⟩]
      exact (P.PD E).Fil_G _ _ _ (hxF k j)
    have h1 := congrFun (hD _ (hx k).1 σ hσ) i
    conv_rhs => rw [← h1]
    simp only [twAct, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum _ _ _ (fun j _ => by
      rw [← Algebra.smul_def]
      exact ((P.PD E).Fil (u k)).smul_of_tower_mem _ (hg j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, (hsy _).2.1 _ _ (hg j),
      (hsy _).2.2.2 σ _ (hxF k j), IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
    have hc : ∀ c : Om l, (c : PadicComplex l) = algebraMap (Om l) (PadicComplex l) c :=
      fun _ => rfl
    rw [hc]
    exact mul_left_comm _ _ _
  refine ⟨fun k i => sy (u k) (x k i), u, ?_, fun k => ⟨x k, (hx k).1, hxF k, fun h => ?_⟩, hact⟩
  · refine GlobalTheory.T.serreTate_linearIndependent_of_weightwise l AI.actC P.χQ (GK E) E.1 ?_ d d _ _ u hact ?_
    · intro i y hy
      have := GlobalTheory.T.tate_invariants_cyclotomic_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs i y
        (by intro g hg; apply hy; unfold GK; rw [hE]; exact hg)
      rwa [hE]
    · intro a c hc h0
      refine hind a c hc fun i _ => ?_
      have hm : ∀ k, c k • x k i ∈ (P.PD E).Fil a := by
        intro k
        by_cases hk : u k = a
        · exact Submodule.smul_mem _ _ (hk ▸ hxF k i)
        · rw [hc k hk, zero_smul]; exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      refine ((hsy a).2.2.1 _ (Submodule.sum_mem _ fun k _ => hm k)).1 ?_
      rw [hsum a _ _ fun k _ => hm k]
      have h1 := congrFun h0 i
      rw [Finset.sum_apply, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : u k = a
      · subst hk
        exact (by rw [Pi.smul_apply, Algebra.smul_def]; exact (hsy _).2.1 _ _ (hxF k i))
      · simp only [Pi.smul_apply, hc k hk, zero_smul, ZeroMemClass.coe_zero, smul_eq_mul]
        rw [((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)]
        simp
  · have := hind (u k) (Pi.single k 1) (fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e])) _)
      (by
        intro i _
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h i) k
    simp at this


set_option maxHeartbeats 1600000 in
theorem htBasis_of_isCrys (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hEs : E.1 = Ks K s) (hle : K.1 ≤ E.1) (LL : FinExt l)
    (h7K : fontCore (P.PD K)) (h7E : fontCore (P.PD E))
    (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hcrys : IsCrys (P.PD E) (T'.ρ.comp (Subgroup.inclusion (GK_le hle))))
    {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T' M A)
    (m : ℕ) (hm : s ≤ m) :
    {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
      DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a}.Finite ∧
    HTBasis AI.actC P.χQ (Gj K m) M
      {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a} := by
  have hLL : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨bV, hbV⟩ := GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices l K LL T' d M A hM
  let ρ' : Representation ↥LL.1 ↥(GK E) T'.V := T'.ρ.comp (Subgroup.inclusion (GK_le hle))
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T'.V, ρ := T'.ρ, cont := T'.cont }
  let AE : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T'.V, ρ := ρ'
      cont := fun x => (T'.cont x).comp (continuous_inclusion (GK_le hle)) }
  have hK := h7K _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AK
  have hE := h7E _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AE
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  refine ⟨GlobalTheory.T.finite_setOf_inf_filtration_ne_succ _ _ (DdR (P.PD K) T'.ρ) (fun a => FilV (P.PD K) a) hK.2.1.1 hanti, ?_⟩
  classical
  let M0 : GQ l → Matrix (Fin d) (Fin d) ℚ_[l] := fun g =>
    if hg : g ∈ GK K then Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i else 0
  have hM0 : ∀ g (hg : g ∈ GK K), M0 g = Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i :=
    fun g hg => dif_pos hg
  have hmul : ∀ g ∈ GK K, ∀ g' ∈ GK K, M0 (g * g') = M0 g * M0 g' := by
    intro g hg g' hg'
    rw [hM0 g hg, hM0 g' hg', hM0 _ (mul_mem hg hg')]
    have key : ∀ γ : ↥(GK K), (Matrix.of fun i j => bV.repr (T'.ρ γ (bV j)) i) =
        LinearMap.toMatrix bV bV ((T'.ρ γ).restrictScalars ℚ_[l]) := fun γ => by
      ext i j
      rw [LinearMap.toMatrix_apply]; rfl
    have hcomp : (T'.ρ ⟨g * g', mul_mem hg hg'⟩).restrictScalars ℚ_[l] =
        (T'.ρ ⟨g, hg⟩).restrictScalars ℚ_[l] ∘ₗ (T'.ρ ⟨g', hg'⟩).restrictScalars ℚ_[l] := by
      refine LinearMap.ext fun v => ?_
      exact LinearMap.congr_fun (map_mul T'.ρ ⟨g, hg⟩ ⟨g', hg'⟩) v
    rw [key, key, key, hcomp]
    exact LinearMap.toMatrix_comp bV bV bV _ _
  obtain ⟨ΦE, -, hΦE⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD E) ρ' bV
  obtain ⟨DE, hDE, hfin, hdim⟩ := GlobalTheory.T.deRham_invariants_coordinates_finrank_eq (P.PD E) ρ' bV hLL hE.2.1.1 (hE.2.2 hcrys) ΦE hΦE
  have hinv : ∀ y ∈ DE, ∀ g ∈ GK E,
      ((M0 g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y := by
    intro y hy g hg
    have := (hDE y).1 hy ⟨g, hg⟩
    simp only [P.PD_actdR] at this
    rw [hM0 g (GK_le hle hg)]
    exact this
  obtain ⟨e, u, hli, hu, hact⟩ := basis_of_invariants P AI Θ K s hs E hEs M0 DE
    hinv hfin hdim
  have hFil : ∀ a x, x ∈ (P.PD E).Fil a ↔ x ∈ (P.PD K).Fil a := fun a x =>
    Set.ext_iff.1 (P.PD_Fil E K a) x
  refine ⟨e, u, hli, fun k => ?_, fun σ hσ k => ?_⟩
  · obtain ⟨y, hy, hy1, hy2⟩ := hu k
    simp only [hFil] at hy1 hy2
    obtain ⟨z, hz, hz1, hz2⟩ := GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt l P K E hle d M0 hmul (u k) y (hinv y hy) hy1 hy2
    obtain ⟨Φ, h1, h2⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro heq
    have hmem : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := by
      refine ⟨?_, (h1 _ _).2 (by simpa using hz1)⟩
      simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply]
      have := hz g g.2
      rw [hM0 g g.2] at this
      simp only [P.PD_actdR]
      exact this
    have hmem' : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) := by
      have heq' : DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) =
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := heq
      rw [heq']; exact hmem
    exact hz2 (by simpa using (h1 _ _).1 hmem'.2)
  · have hσE : σ ∈ GK E := by
      refine IntermediateField.fixingSubgroup_le (?_ : E.1 ≤ Ks K m) hσ
      rw [hEs]
      refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      change x ^ (l ^ (s + n)) = 1
      rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]
    have hσK : σ ∈ GK K := GK_le hle hσE
    have hMσ : M σ = (M0 σ).map (algebraMap ℚ_[l] (PadicComplex l)) := by
      rw [hM0 σ hσK]
      ext i j
      exact hbV ⟨σ, hσK⟩ i j
    have := hact σ hσE k
    unfold twAct at this ⊢
    rw [hMσ]
    exact this

theorem exists_htBasis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  intro D HW F h7 l _ K s LL h S E' T hcr d M A hM m hm
  obtain ⟨Θ⟩ := GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData D l
  obtain ⟨E, hEs⟩ : ∃ E : FinExt l, E.1 = Ks K s :=
    ⟨⟨Ks K s, GlobalTheory.MemLoc.finiteDimensional_Ks_of_finExt K s⟩, rfl⟩
  have hle : K.1 ≤ E.1 := hEs ▸ h.2.2.1
  exact htBasis_of_isCrys (D.loc l) (D.locA l) Θ K s ⟨h.1, h.2.1⟩ E hEs hle LL (h7 l K) (h7 l E) T
    (GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h) E hEs hle T hcr)
    M A hM m hm

end GlobalTheory.HTBasisEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  first | exact @GlobalTheory.HTBasisEx.exists_htBasis | exact GlobalTheory.HTBasisEx.exists_htBasis | (intros; apply GlobalTheory.HTBasisEx.exists_htBasis <;> assumption)
end

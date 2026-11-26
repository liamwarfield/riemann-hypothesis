module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentation

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TUnitcent
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

open MeasureTheory in
theorem UpperTheory.Lit.Cas.unitcent :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), IsSmooth π → π.IsIrreducible → CoeffLp p π → UnitaryCentral π := by
  intro k _ _ _ _ N V _ _ π p hs hirr hLp t c hc
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, hKo, hKc, -⟩ := GlobalTheory.SqIntUnit.compactOpen_basis k N Set.univ Filter.univ_mem
  obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv
  haveI hQ : IsTopologicalGroup (GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)) := inferInstance
  letI : MeasurableSpace (AdGL k N) := borel _
  haveI : BorelSpace (AdGL k N) := ⟨rfl⟩
  let q : GL (Fin N) k → AdGL k N := QuotientGroup.mk
  have hqc : Continuous q := continuous_quot_mk
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let K₀ : TopologicalSpace.PositiveCompacts (AdGL k N) :=
    ⟨⟨q '' (K : Set (GL (Fin N) k)), hKc.image hqc⟩, by
      refine ⟨q 1, ?_⟩
      rw [(hqo _ hKo).interior_eq]
      exact ⟨1, K.one_mem, rfl⟩⟩
  have hopen : IsOpen {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l} := by
    have h1 := l.2
    change IsOpen {g | π.dual g l = l} at h1
    have h2 : {g : GL (Fin N) k | (l : Module.Dual ℂ V) ∘ₗ π g = l} = (fun g => g⁻¹) ⁻¹' {g | π.dual g l = l} := by
      ext g
      simp [Representation.dual_apply, Module.Dual.transpose_apply]
    rw [h2]
    exact h1.preimage continuous_inv
  obtain ⟨F, hF, -⟩ := hLp (MeasureTheory.Measure.haarMeasure K₀)
    (MeasureTheory.Measure.isHaarMeasure_haarMeasure K₀) v l hopen
  have hz : (Matrix.GeneralLinearGroup.scalar (Fin N) t) ∈ Subgroup.center (GL (Fin N) k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_smul, Matrix.smul_mul, mul_comm]
  have hq : ((Matrix.GeneralLinearGroup.scalar (Fin N) t : GL (Fin N) k) : AdGL k N) = ((1 : GL (Fin N) k) : AdGL k N) := by
    rw [QuotientGroup.eq]
    simpa using hz
  have e1 := hF (Matrix.GeneralLinearGroup.scalar (Fin N) t)
  have e2 := hF 1
  rw [hq, e2, hc v, map_one] at e1
  simp only [Module.End.one_apply, map_smul, norm_smul] at e1
  have hlv : 0 < ‖(l : Module.Dual ℂ V) v‖ := norm_pos_iff.mpr hl
  have h3 : (‖c‖ - 1) * ‖(l : Module.Dual ℂ V) v‖ = 0 := by
    rw [sub_mul, one_mul, ← e1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TProdExp
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarProd
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.scalarProd :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h : ℕ) (y : Fin h → IrrGL (k := k)) (x : IrrGL (k := k)) (hc : ∑ i, (y i).1 = x.1) (t : kˣ) (c : Fin h → ℂ), (∀ i, ScalarBy (y i) t (c i)) → jhMult x.rep (prodIrr y hc) ≠ 0 → ScalarBy x t (∏ i, c i) := by
  intro k _ _ _ _ h y x hc t c hy hm w
  exact GlobalTheory.SmGL.Model.scalar_of_isSubquotient (jhMult_ne_zero_iff.1 hm)
    (UpperTheory.Lit.Cas.scalarFull k h x.1 y hc t c hy) w
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSplit
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Cas.TSplit

private theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

private theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hne
  apply h
  unfold jhMult
  refine nonpos_iff_eq_zero.mp (iSup_le fun r => iSup_le fun hr => ?_)
  obtain ⟨S, T, -, -, hST⟩ := hr
  cases r with
  | zero => simp
  | succ n => exact (hne ⟨S 0, T 0, hST 0⟩).elim

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne _ _ _ hab]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    exact fun h => absurd h hab

private theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

private theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  ext
  rw [val_deltaHalf]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    simp only [modulus, Fin.prod_univ_two, nabs_det_scalar, modExp]
    simp only [Finset.sum_filter, Fin.sum_univ_two]
    simp
    have hp : nabs k t ≠ 0 := ne_of_gt (nabs_pos' k t)
    have he : (nabs k t ^ d 1) ^ d 0 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast]
    have he' : (nabs k t ^ d 0) ^ d 1 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [zpow_mul, zpow_natCast, zpow_natCast]
    rw [he, he']
    exact mul_inv_cancel₀ (zpow_ne_zero _ hp)
  rw [hm]
  simp

private theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL (k := k)) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add (f := _), hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

private theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have key : E.toLinearEquiv (ρ g (E.toLinearEquiv.symm w)) =
      σ g (E.toLinearEquiv (E.toLinearEquiv.symm w)) :=
    Representation.IntertwiningMap.isIntertwining ρ σ E.toIntertwiningMap g _
  simp only [hρ, hσ, map_smul, LinearEquiv.apply_symm_apply] at key
  have h0 : (c' - c) • w = 0 := by rw [sub_smul, key, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hw)

end UpperTheory.Lit.Cas.TSplit

open UpperTheory.Lit.Cas.TSplit in
theorem UpperTheory.Lit.Cas.split :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ScalarBy (x 0) t c0 → ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hπ h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero hj
  set g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, leviEmb_scalar, deltaHalf_scalar, hπ, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]
  have hsub := subQuot_apply_of_smul S T hjac
  have hpi := piTensor_apply_of_smul x g ![c0, c1] (by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v)
  haveI : Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ (fun a => Model.nontrivial_of_isIrreducible (x a).2.rep.irr)
  have := smul_eq_of_equiv E hsub hpi
  simpa [Fin.prod_univ_two] using this
end

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem jac_equiv_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    Nonempty ((jac e π).Equiv (jac e τ)) := by
  refine ⟨Representation.Equiv.mk' (jacMap e φ.toIntertwiningMap)
    (jacMap e φ.symm.toIntertwiningMap) ?_ ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ.symm (φ v)) = Submodule.Quotient.mk v
      simp
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ (φ.symm v)) = Submodule.Quotient.mk v
      simp

private theorem cell_exp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hC : CasselmanNecSq k) (δ : IrrGL (k := k))
    (h1 : 1 ≤ δ.1) (h2 : IsSqIntCoeff δ.rep) (y : Fin 2 → IrrGL (k := k)) (hr : ∑ j, (y j).1 = δ.1)
    (hj : jm y hr δ.rep ≠ 0) (t : kˣ) (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
    (a : Fin 2 → ℂ) (ha : ∀ j, ScalarBy (y j) t (a j)) : ‖a 0‖ ≤ 1 ∧ ‖a 0‖ * ‖a 1‖ = 1 := by
  obtain ⟨⟨c, hc⟩, -, -⟩ := schur hA k δ t
  have hu : ‖c‖ = 1 := unitcent k δ.1 _ δ.rep 2 δ.snd.rep.smooth δ.snd.rep.irr h2 t c hc
  have hprod : a 0 * a 1 = c := split k δ.1 _ δ.rep y hr hj t c (a 0) (a 1) hc (ha 0) (ha 1)
  have hnorm : ‖a 0‖ * ‖a 1‖ = 1 := by rw [← norm_mul, hprod, hu]
  refine ⟨?_, hnorm⟩
  by_cases h0 : (y 0).1 = 0
  · rw [(schur hA k (y 0) t).2.2 (a 0) h0 (ha 0), norm_one]
  by_cases h1' : (y 1).1 = 0
  · rw [(schur hA k (y 1) t).2.2 (a 1) h1' (ha 1), norm_one, mul_one] at hnorm
    exact hnorm.le
  have hpos : ∀ j : Fin 2, 0 < (y j).1 :=
    Fin.forall_fin_two.2 ⟨Nat.pos_of_ne_zero h0, Nat.pos_of_ne_zero h1'⟩
  have hE := hC δ.1 δ.rep h1 δ.snd.rep.smooth δ.snd.rep.irr h2 2 y hr hpos hj
  have hlt := (hE t ht a ha).1 0 (by norm_num)
  have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
  rw [hf, Finset.prod_singleton] at hlt
  exact hlt.le

theorem UpperTheory.Lit.Cas.prodExp :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CasselmanNecSq k → ∀ (h N : ℕ) (δ : Fin h → IrrGL (k := k)) (hd : ∑ i, (δ i).1 = N), (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible → Nonempty (π.Equiv (prodIrr δ hd)) → UnitaryCentral π ∧ MaxExpWeak π := by
  intro hG hBZ hA k _ _ _ _ hC h N δ hd hδ V _ _ π hirr hφ
  obtain ⟨φ⟩ := hφ
  haveI := nontrivial_of_irreducible hirr
  constructor
  · intro t c hc
    choose b hb using fun i => (schur hA k (δ i) t).1
    have hbn : ∀ i, ‖b i‖ = 1 := fun i =>
      unitcent k (δ i).1 _ (δ i).rep 2 (δ i).snd.rep.smooth (δ i).snd.rep.irr (hδ i).2 t (b i) (hb i)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hφv : φ.toLinearEquiv v ≠ 0 := by
      rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
    have e1 : φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v)
        = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) :=
      LinearMap.congr_fun
        (φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.scalar (Fin N) t)) v
    have e2 : c • φ.toLinearEquiv v = (∏ i, b i) • φ.toLinearEquiv v :=
      calc c • φ.toLinearEquiv v = φ.toLinearEquiv (c • v) :=
            (LinearEquiv.map_smul φ.toLinearEquiv c v).symm
        _ = φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v) :=
            congrArg _ (hc v).symm
        _ = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) := e1
        _ = (∏ i, b i) • φ.toLinearEquiv v := scalarFull k h N δ hd t b hb _
    have hcb : c = ∏ i, b i := smul_left_injective ℂ hφv e2
    rw [hcb, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hbn i)
  · intro x hx hpos hj
    have hjm : jm x hx (prodIrr δ hd) ≠ 0 := by
      obtain ⟨ψ⟩ := jac_equiv_of_equiv (stdBlocks (fun a => (x a).1) hx) φ
      unfold jm at hj ⊢
      rwa [← jhMult_congr_right _ ψ]
    obtain ⟨y, hr, hcc, hyj, hxj⟩ := cells hG hBZ k h N δ hd x hx hjm
    intro t ht c hcx
    choose a ha using fun i j => (schur hA k (y i j) t).1
    have hcj : ∀ j, c j = ∏ i, a i j := fun j =>
      (schur hA k (x j) t).2.1 _ _ (hcx j)
        (scalarProd k h (fun i => y i j) (x j) (hcc j) t (fun i => a i j) (fun i => ha i j) (hxj j))
    have hcell : ∀ i, ‖a i 0‖ ≤ 1 ∧ ‖a i 0‖ * ‖a i 1‖ = 1 := fun i =>
      cell_exp hA hC (δ i) (hδ i).1 (hδ i).2 (y i) (hr i) (hyj i) t ht (a i) (ha i)
    have n0 : ‖c 0‖ ≤ 1 := by
      rw [hcj 0, norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (hcell i).1)
    have n01 : ‖c 0‖ * ‖c 1‖ = 1 := by
      rw [hcj 0, hcj 1, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => (hcell i).2)
    refine ⟨fun j hj' => ?_, by rw [Fin.prod_univ_two]; exact n01⟩
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
    rw [hf, Finset.prod_singleton]
    exact n0
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCosocleUnit
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem exists_compl_of_admissible {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hs : IsSmooth ρ) (hun : IsUnitarisable ρ) (W : Subrepresentation ρ) (hW : IsAdmissible W.toRepresentation) :
    ∃ W' : Subrepresentation ρ, (∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule → v = 0) ∧
      ∀ v, ∃ w ∈ W.toSubmodule, v - w ∈ W'.toSubmodule := by
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  refine ⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hinv W, ?_, ?_⟩
  · intro v hv hv'
    by_contra hne
    have h1 : B v v = 0 := hv' v hv
    have h2 := hpos v hne
    rw [h1] at h2
    simp at h2
  · intro v
    obtain ⟨K, hKo, hKc, hKU⟩ := hbasis _ ((hs v).mem_nhds (by simp))
    have hfd := hW.2 K hKo hKc
    obtain ⟨t, ht⟩ := (Module.Finite.iff_fg.mp hfd).map W.toSubmodule.subtype
    have hM : ∀ s, s ∈ Submodule.span ℂ (t : Set V) ↔ s ∈ W.toSubmodule ∧ ∀ k ∈ K, ρ k s = s := by
      intro s
      rw [ht, Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hx
        exact ⟨x.2, fun k hk => congrArg Subtype.val (hx k hk)⟩
      · rintro ⟨hsW, hsK⟩
        refine ⟨⟨s, hsW⟩, ?_, rfl⟩
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff]
        intro k hk
        exact Subtype.ext (hsK k hk)
    obtain ⟨w, hw, hperp⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hpos t v
    refine ⟨w, ((hM w).mp hw).1, ?_⟩
    intro w' hw'
    have hvK : ∀ k ∈ K, ρ k v = v := fun k hk => hKU hk
    have huK : ∀ k ∈ K, ρ k (v - w) = v - w := fun k hk => by
      rw [map_sub, hvK k hk, ((hM w).mp hw).2 k hk]
    refine GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hinv K hKc W (v - w) huK (fun s hs' => hperp s ?_) w' hw' (hs w')
    rw [hM]
    exact ⟨hs'.1, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K s).mp hs'.2⟩

private theorem isCoatom_of_compl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {S T : Subrepresentation ρ} (hS : IsAtom S) (hST : ∀ v, v ∈ S.toSubmodule → v ∈ T.toSubmodule → v = 0)
    (hsum : ∀ v, ∃ w ∈ S.toSubmodule, v - w ∈ T.toSubmodule) : IsCoatom T := by
  constructor
  · intro hT
    obtain ⟨s, hsS, hs0⟩ : ∃ s ∈ S.toSubmodule, s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hS.1
      apply Subrepresentation.ext
      ext v
      show v ∈ S.toSubmodule ↔ v ∈ (⊥ : Submodule ℂ V)
      rw [Submodule.mem_bot]
      exact ⟨hcon v, fun h => h ▸ S.toSubmodule.zero_mem⟩
    apply hs0 (hST s hsS _)
    rw [hT]
    show s ∈ (⊤ : Submodule ℂ V)
    trivial
  · intro U hTU
    obtain ⟨hle, u, huU, huT⟩ := SetLike.lt_iff_le_and_exists.mp hTU
    obtain ⟨w, hwS, hwT⟩ := hsum u
    have hwU : w ∈ U.toSubmodule := by
      rw [← sub_sub_cancel u w]
      exact U.toSubmodule.sub_mem huU (hle hwT)
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply huT
      rw [sub_zero] at hwT
      exact hwT
    have hSU : S ≤ U := by
      have hinf : S ⊓ U = S := (hS.le_iff.mp inf_le_left).resolve_left (by
        intro h
        apply hw0
        have hm : w ∈ (S ⊓ U).toSubmodule := ⟨hwS, hwU⟩
        rw [h] at hm
        exact (Submodule.mem_bot ℂ).mp hm)
      rw [← hinf]
      exact inf_le_right
    apply Subrepresentation.ext
    ext v
    show v ∈ U.toSubmodule ↔ v ∈ (⊤ : Submodule ℂ V)
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨w', hw'S, hw'T⟩ := hsum v
    have hadd := U.toSubmodule.add_mem (hSU hw'S) (hle hw'T)
    simpa using hadd

private theorem equiv_of_isCosocle (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin N) k) X) (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (hfl : HasFiniteLength π) (hun : IsUnitarisable π) (hc : IsCosocle σ π) : Nonempty (σ.Equiv π) := by
  obtain ⟨-, f, hfs, hker⟩ := hc
  have hinj : Function.Injective f := by
    intro v w hvw
    by_contra hne
    have hmem : v - w ∈ (Representation.IntertwiningMap.ker π σ f).toSubmodule := by
      show v - w ∈ LinearMap.ker f.toLinearMap
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hvw
    have hK : Representation.IntertwiningMap.ker π σ f ≠ ⊥ := by
      intro hK0
      rw [hK0] at hmem
      exact hne (sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp hmem))
    haveI := ((hasFiniteLength_iff_wellFounded π).mp hfl).2
    obtain ⟨S, hS, hSK⟩ := (eq_bot_or_exists_atom_le _).resolve_left hK
    let ι : S.toRepresentation.IntertwiningMap π :=
      (S.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => rfl)
    have hSs : IsSmooth S.toRepresentation :=
      IsSubquotient.isSmooth (IsSubquotient.of_injective ι Subtype.val_injective) hs
    have hSadm : IsAdmissible S.toRepresentation :=
      (hBZ k).1 (Fin N) _ S.toRepresentation hSs (GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS)
    obtain ⟨T, hST, hsum⟩ := exists_compl_of_admissible π
      (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun S hSadm
    have hTK := hker T (isCoatom_of_compl hS hST hsum)
    apply hS.1
    apply Subrepresentation.ext
    ext s
    show s ∈ S.toSubmodule ↔ s ∈ (⊥ : Submodule ℂ V)
    rw [Submodule.mem_bot]
    constructor
    · intro hs'
      apply hST s hs'
      rw [hTK]
      exact hSK hs'
    · rintro rfl
      exact S.toSubmodule.zero_mem
  exact ⟨(equivOfBijective f ⟨hinj, hfs⟩).symm⟩

theorem UpperTheory.Lit.Cas.cosocleUnit :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), (∀ a, IsUnitarisable (x a).rep) → IsCosocle π (prodIrr x hd) → Nonempty (π.Equiv (prodIrr x hd)) := by
  intro hBZ k _ _ _ _ h N x hd V _ _ π hun hc
  have hIA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k' _ _ _ _ n W _ _ ρ hs hi => (hBZ k').1 (Fin n) W ρ hs hi
  have hsm : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor (fun a => (x a).snd.rep.smooth)
  have hfl0 : HasFiniteLength (piTensor fun a => (x a).rep) :=
    hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hIA x)
  have hfl : HasFiniteLength (prodIrr x hd) :=
    (hBZ k).2.2.1 (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) _ _ hsm hfl0
  exact equiv_of_isCosocle hBZ π (prodIrr x hd) (isSmooth_prodIrr x hd) hfl
    (UnitInd.isUnitarisable_multiProd _ hun) hc
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnSuff
open Filter Topology MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel GlobalTheory.CompanionTheory.CoeffBound

namespace UpperTheory.Lit.Cas

def HeckeWeak {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, 0 < j → j < N → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)),
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N j)) T → ∀ μ : ℂ, T.HasEigenvalue μ →
      ‖μ‖ ≤ (Nat.card 𝓀[k] : ℝ) ^ (-(((j * (N - j) : ℕ) : ℝ) / 2))

theorem exists_radius_rpow {q p : ℝ} (hq : 1 < q) (hp : 2 < p) (a : ℕ) (ha : 0 < a) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ q ^ (-((a : ℝ) / 2)) < ρ ∧ q ^ a * ρ ^ p < 1 := by
  have hq0 : 0 < q := by linarith
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hs : (0 : ℝ) < (2 + p) / 2 := by linarith
  refine ⟨q ^ (-((a : ℝ) / ((2 + p) / 2))), (Real.rpow_pos_of_pos hq0 _).le, ?_, ?_⟩
  · refine Real.rpow_lt_rpow_of_exponent_lt hq (neg_lt_neg ?_)
    exact div_lt_div_of_pos_left ha' (by norm_num) (by linarith)
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
    have : (a : ℝ) < (a : ℝ) / ((2 + p) / 2) * p := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hs]
      exact mul_lt_mul_of_pos_left (by linarith) ha'
    linarith

theorem norm_le_of_norm_mul_cpow_le (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ ≤ 1) : ‖μ‖ ≤ (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, le_div_iff₀ hp]
  exact h

theorem heckeWeak_of_maxExpWeak (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : MaxExpWeak π) : HeckeWeak π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using (Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _).le
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := GlobalTheory.T.hecke_operator_jacquet_eigen_left k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := GlobalTheory.T.hecke_operator_jacquet_eigen_right k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (GlobalTheory.T.uniformizer_pow_tendsto_zero k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_le_of_norm_mul_cpow_le (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

theorem coeff_bound_rpow (p : ℝ) (hp : 2 < p) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → HeckeWeak π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ p < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hq1 : (1 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])
  have hrad := fun j : Fin (N - 1) => exists_radius_rpow hq1 hp (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))
    (Nat.mul_pos (by omega) (by omega))
  choose ρ hρ0 hρb hρp using hrad
  have hρe : ∀ (j : Fin (N - 1)) (μ : ℂ), (T j).HasEigenvalue μ → ‖μ‖ < ρ j := fun j μ hμ =>
    (hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ).trans_lt (hρb j)
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact hρp j
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

theorem lintegral_rpow_lt_top_of_cover {p : ℝ} (hp : 0 ≤ p) {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hb : ∀ i j, 0 ≤ b i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ p * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ p ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ r : ι × κ, A r.1 r.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ p ∂μ ≤ ∑' r : ι × κ, ∫⁻ x in A r.1 r.2, ‖F x‖ₑ ^ p ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ r : ι × κ, ∫⁻ x in A r.1 r.2, ‖F x‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal (b r.1 r.2 ^ p * w r.1 r.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ p ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ p) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hF i j x hx) hp)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (Real.rpow_nonneg (hb i j) _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ p * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (Real.rpow_nonneg (hb i j) _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem rpow_mul_pow_eq {r : ℕ} (q p : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (C : ℝ) (hC : 0 ≤ C) :
    (C * ∏ j, ρ j ^ g j) ^ p * q ^ (∑ j, g j * e j) = C ^ p * ∏ j, (q ^ e j * ρ j ^ p) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ p) ^ g j = (∏ j, ρ j ^ g j) ^ p := by
    have hprod : ∀ s : Finset (Fin r), (∏ j ∈ s, ρ j ^ g j) ^ p = ∏ j ∈ s, (ρ j ^ g j) ^ p := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        rw [Real.mul_rpow (pow_nonneg (hρ a) _) (Finset.prod_nonneg fun j _ => pow_nonneg (hρ j) _), ih]
    rw [hprod]
    exact Finset.prod_congr rfl fun j _ => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hρ j), mul_comm, Real.rpow_mul (hρ j), Real.rpow_natCast]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, Real.mul_rpow hC (Finset.prod_nonneg fun j _ => pow_nonneg (hρ j) _), mul_assoc,
    mul_comm (q ^ _)]

theorem coeffLp_of_heckeWeak (p : ℝ) (hp : 2 < p) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    HeckeWeak π → CoeffLp p π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  have hp0 : 0 ≤ p := by linarith
  unfold CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  have hmeas : AEStronglyMeasurable (fun q : AdGL k N => ‖l (π q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_⟩
  change eLpNorm (fun q : AdGL k N => ‖l (π q.out v)‖) (ENNReal.ofReal p) μ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by simpa using (by linarith : 0 < p)) ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hp0]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := ⟨fun x y => by
      induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
      rw [Subsingleton.elim x y]⟩
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_rpow_lt_top_of_cover hp0 μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ _ => norm_nonneg _) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ u : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), 0 ≤ C ∧ (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ p < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (u.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * u.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨u, hu'⟩
    obtain ⟨h1, h2⟩ := hsK u hu'
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK u.1 u.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := coeff_bound_rpow p hp k N V π hs ha hH m hm (π u.2 v) hf (l ∘ₗ π u.1) hli
    have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
    refine ⟨C, ρ, hC, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hC0 hρ0 hρ1 hbound using key
  refine lintegral_rpow_lt_top_of_cover hp0 μ _
    (fun (u : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = u.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * u.1.2})
    ?_ (fun u g => C u * ∏ j, ρ u j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (fun u g => mul_nonneg (hC0 u) (Finset.prod_nonneg fun j _ => pow_nonneg (hρ0 u j) _))
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu', g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨u, hu'⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro u g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound u g a ha' b hb
  · intro u g
    obtain ⟨h1, h2⟩ := hsK u.1 u.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm u.1.1 u.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro u
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ u j ^ p)
      (fun j => mul_nonneg (by positivity) (Real.rpow_nonneg (hρ0 u j) _)) (hρ1 u)
    exact (h.mul_left (C u ^ p)).congr fun g => (rpow_mul_pow_eq _ p _ g _ (hρ0 u) _ (hC0 u)).symm

theorem casselmanSuffTemp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : CasselmanSuffTemp k := by
  intro N V _ _ π _ hs hi hu he ε hε
  exact @coeffLp_of_heckeWeak (2 + ε) (by linarith) k _ _ _ _ N V _ _ π hs hi (hA k N V π hs hi) hu
    (heckeWeak_of_maxExpWeak k N V π hs hi hA hF he)

end UpperTheory.Lit.Cas
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTCentred
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.centred :
    GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → (∀ (t : kˣ) (c : ℂ), ScalarBy y t c → ‖c‖ = 1) → IsSqIntCoeff y.rep := by
  intro H HA k _ _ _ _ _ Δ δ h hu
  have hpos : 0 < δ.1 := by
    obtain ⟨hd, -⟩ := h
    rw [← hd]
    have h1 : ∀ a, (Δ.term a).1 = Δ.first.1 := fun a => rfl
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_pos Δ.len_pos Δ.isCusp_first.1
  obtain ⟨χ, hχ, hsq⟩ := (H k δ hpos).2 ⟨Δ, h⟩
  let e := δ.twEquiv χ hχ
  let τ := (δ.tw χ hχ).rep
  have he : ∀ g w, e.toLinearEquiv.symm (τ g w) =
      ((detChar (Fin δ.1) χ g : ℂˣ) : ℂ) • δ.rep g (e.toLinearEquiv.symm w) := fun g w => by
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective w
    have := e.toIntertwiningMap.isIntertwining _ _ g u
    rw [LinearEquiv.symm_apply_apply]
    refine e.toLinearEquiv.injective ?_
    rw [LinearEquiv.apply_symm_apply]
    exact this.symm
  have hτ : UnitaryCentral τ :=
    UpperTheory.Lit.Cas.unitcent k _ _ τ 2 (δ.tw χ hχ).2.rep.smooth (δ.tw χ hχ).2.rep.irr hsq
  have hχ1 : ∀ a : kˣ, ‖((χ a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    let z := Matrix.GeneralLinearGroup.scalar (Fin δ.1) a
    obtain ⟨c, hc⟩ := (UpperTheory.Lit.Cas.schur HA k δ a).1
    have hc1 := hu a c hc
    have hz1 : ‖((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) * c‖ = 1 := by
      refine hτ a _ fun w => ?_
      refine e.toLinearEquiv.symm.injective ?_
      refine (he z w).trans ?_
      rw [map_smul, mul_smul]
      exact congrArg _ (hc _)
    rw [norm_mul, hc1, mul_one] at hz1
    have hdz : ((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) ^ δ.1 := by
      have hdet : Matrix.GeneralLinearGroup.det z = a ^ δ.1 := Units.ext (by
        simp [z, Matrix.GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal])
      rw [detChar_apply, hdet, map_pow, Units.val_pow_eq_pow_val]
    rw [hdz, norm_pow] at hz1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hz1
  intro m bm μ hμ v ℓ hℓ'
  let l' : Module.Dual ℂ _ := ℓ ∘ₗ e.toLinearEquiv.symm.toLinearMap
  have hc : ∀ g, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ := fun g => by
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul,
      norm_mul]
  have hFc0 : ∀ g : GL (Fin δ.1) k, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ :=
    fun g => hc g
  have hopen : IsOpen {g : GL (Fin δ.1) k | l' ∘ₗ τ g = l'} := by
    have hk : IsOpen ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) := hχ.detChar
    refine isOpen_iff_mem_nhds.2 fun g hg => ?_
    have hg' : l' ∘ₗ τ g = l' := hg
    have hU : {x | ℓ ∘ₗ δ.rep x = ℓ} ∩ ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact Filter.inter_mem (hℓ'.mem_nhds (by show ℓ ∘ₗ δ.rep 1 = ℓ; rw [map_one, Module.End.one_eq_id, LinearMap.comp_id]))
        (hk.mem_nhds (one_mem _))
    refine Filter.mem_of_superset ((continuous_const_mul g⁻¹).continuousAt.preimage_mem_nhds hU) fun x hx => ?_
    obtain ⟨h1, h2⟩ := hx
    have h1' : ℓ ∘ₗ δ.rep (g⁻¹ * x) = ℓ := h1
    have h2' : detChar (Fin δ.1) χ (g⁻¹ * x) = 1 := h2
    show l' ∘ₗ τ x = l'
    have hx' : τ x = τ g * τ (g⁻¹ * x) := (congrArg τ (mul_inv_cancel_left g x)).symm.trans (map_mul τ g (g⁻¹ * x))
    rw [hx', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hg']
    ext w
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine (congrArg ℓ (he (g⁻¹ * x) w)).trans ?_
    rw [map_smul, h2', Units.val_one, one_smul]
    exact LinearMap.congr_fun h1' _
  obtain ⟨F, hF, hL⟩ := @hsq m bm μ hμ (e.toLinearEquiv v) l' hopen
  refine ⟨F, fun g => ?_, hL⟩
  refine ((hF g).trans (hFc0 g)).trans ?_
  rw [detChar_apply, hχ1, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTOrderfree
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_irreducible_GL_zero : ∃ t : IrrGL (k := k), t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (GlobalTheory.LocGL.Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

private theorem equiv_of_isL [CharZero k] (HM : GlobalTheory.Published.LanglandsMultisegments) {𝔪 : Multiset (Segment k)}
    {n : ℕ} (c c' : IrrCl (GL (Fin n) k)) (hc : IsL 𝔪 (IrrGL.rep ⟨n, c⟩))
    (hc' : IsL 𝔪 (IrrGL.rep ⟨n, c'⟩)) : Nonempty (c'.rep.ρ.Equiv c.rep.ρ) := by
  obtain ⟨o, h0, ho⟩ := exists_irreducible_GL_zero (k := k)
  have hd : ∑ a, (![(⟨n, c⟩ : IrrGL (k := k)), o] a).1 = n := by simp [h0]
  have hs := (HM k).2 𝔪 0 ![⟨n, c⟩, o] ⟨n, c'⟩ hd hc ho (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero k (⟨n, c⟩ : IrrGL (k := k)) o h0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨n, c'⟩ : IrrGL (k := k))) (IrrGL.rep (⟨n, c⟩ : IrrGL (k := k))) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  exact (hs2.nonempty_equiv c'.rep.irr c.rep.irr).map fun e => e.symm

private theorem equiv_of_isL' [CharZero k] (HM : GlobalTheory.Published.LanglandsMultisegments) {𝔪 : Multiset (Segment k)}
    {n : ℕ} (p y : IrrRep (GL (Fin n) k)) (hp : IsL 𝔪 p.ρ) (hy : IsL 𝔪 y.ρ) : Nonempty (y.ρ.Equiv p.ρ) := by
  have ep : p.ρ.Equiv p.cl.rep.ρ := equivRep p
  have ey : y.ρ.Equiv y.cl.rep.ρ := equivRep y
  obtain ⟨e⟩ := equiv_of_isL HM p.cl y.cl (hp.of_equiv ep) (hy.of_equiv ey)
  exact ⟨(ey.trans e).trans ep.symm⟩

end

theorem UpperTheory.Lit.Cas.orderfree :
    GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.LanglandsMultisegments → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → IsCosocle π (prodIrr x hd) := by
  intro HC HM k _ _ _ _ _ 𝔪 h N x hd hx V _ _ π hπ
  obtain ⟨y, hy⟩ := HC k 𝔪 h N x hd hx
  have h1 : IsL 𝔪 y.ρ := ⟨h, x, hd, hx, hy⟩
  obtain ⟨e⟩ := equiv_of_isL' HM ⟨V, π, hπ.irr_smooth.2, hπ.irr_smooth.1⟩ y hπ h1
  exact hy.of_equiv e (.refl _)
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace UpperTheory.Lit.Cas

theorem temperedProduct (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hC : GlobalTheory.Published.StandardCosocleGL) (hM : GlobalTheory.Published.LanglandsMultisegments)
    (hS : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.TemperedProductOfSquareIntegrable := by
  intro k _ _ _ _ _ N hN V _ _ π hs hi
  constructor
  · intro ht
    have hO : Zc.LOrderFree k := orderfree hC hM k
    have hSo : Zc.LSocleGL k := GlobalTheory.T.langlands_socle_of_order_free hA (GlobalTheory.T.local_langlands_of_irreducible_admissible hA) hO
    have hL : Zc.LSegExists k := fun Δ => GlobalTheory.TL.exists_segment_representation hA Δ
    obtain ⟨𝔪, h𝔪⟩ := hE k (IrrGL.of π hs hi)
    have h𝔪' : IsL 𝔪 π := h𝔪.of_equiv (IrrGL.equivOf π hs hi).symm
    obtain ⟨h, x, hd, hx, hu⟩ := GlobalTheory.T.tempered_langlands_factors_square_integrable k hSo (Zl.JC.casselmanNecTemp_holds k) hL 𝔪 N π hN hs hi ht h𝔪'
    obtain ⟨Δ, hΔo, hΔ⟩ := hx
    have hsq : ∀ a, IsSqIntCoeff (x a).rep := fun a => centred hS hA k (Δ a) (x a) (hΔ a) (hu a)
    have e := cosocleUnit hBZ k h N x hd V π (fun a => GlobalTheory.T.square_integrable_unitarizable k (x a) (hsq a)) (hO 𝔪 h N x hd ⟨Δ, hΔo, hΔ⟩ π h𝔪')
    refine ⟨h, x, hd, fun a => ⟨?_, hsq a⟩, e⟩
    have h1 := (hΔ a).deg_eq
    have h2 := Nat.mul_pos (Δ a).len_pos (Δ a).d_pos
    simp only [Segment.deg] at h1
    omega
  · rintro ⟨h, δ, hd, hδ, e⟩
    obtain ⟨hu, hw⟩ := prodExp hG hBZ hA k (Zl.JC.casselmanNecSq_holds k) h N δ hd hδ V π hi e
    have H := casselmanSuffTemp hA hF k N π hN hs hi hu hw
    intro ε hε
    exact H ε hε

end UpperTheory.Lit.Cas

end

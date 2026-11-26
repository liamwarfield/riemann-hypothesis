module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_mem_of_unitary_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M)
    (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin k) ℂ) (hf : f ∈ M) : rowAct ℂ g f ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  obtain ⟨P, hP⟩ := exists_poly_rowAct_coef n k f l
  have h0 : P = 0 := eq_zero_of_vanish_unitaryGroup n P fun u hu => by
    rw [← hP]
    exact (Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)
  rw [hP, h0, map_zero]

theorem rowDivClosed_of_rowAct_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ M, rowAct ℂ g f ∈ M) : RowDivClosed M := by
  intro a b j p hp
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  set N := (rowGen ℂ a b p).natDegree + j + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := (Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem height_rowDiv_le {n k : ℕ} (H : ℤ) (a b : Fin n) (j : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (hf : ∀ d ∈ f.support, Finsupp.weight (lhwinHt n k) d ≤ H) :
    ∀ d ∈ (rowDiv ℂ a b j f).support, Finsupp.weight (lhwinHt n k) d ≤ H + j * ((a.val : ℤ) - b.val) := by
  intro e he
  have hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (AddMonoidAlgebra.coeff f d))).coeff j := by
    unfold rowDiv
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Polynomial.finsetSum_coeff]
  rw [mem_support_iff, hs, coeff_sum] at he
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have h1 := lhwinShift_rowGen_monomial ℂ a b d (AddMonoidAlgebra.coeff f d) j hne
  have h2 := hf d hd
  omega

theorem exists_killed_of_rowDivClosed {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin n, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv ℂ a b j v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩
    have := Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd
    have h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _ := Int.ofNat_le.2 this
    exact (Int.self_le_toNat _).trans h2
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab j hj => ?_⟩
  by_contra hne'
  have hH := height_rowDiv_le _ a b j v hvH
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne'
  have hnn := (lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b j v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

theorem dualWeyl_le_of_rowDivClosed {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hle : M ≤ dualWeyl ℂ r n ν) (hM : RowDivClosed M)
    (hne : M ≠ ⊥) : dualWeyl ℂ r n ν ≤ M := by
  obtain ⟨v, hvM, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℂ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hhw : hw ℂ hn ν ∈ M := e ▸ M.smul_mem _ hvM
  refine (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hhw
  | cons x w ih => exact hM _ _ _ _ ih

theorem isIrreducible_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    (smallRep (unitaryIncl n) mu).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hS)
  refine Or.inr (Subrepresentation.ext ?_)
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := S.toSubmodule.map (nablaSq ℂ n mu).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, S.apply_mem_toSubmodule t hf, rfl⟩
    have h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f := rfl
    rw [h2] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype
    (e.trans (Submodule.map_bot _).symm))
  have hle := dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M
    (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨g, hg, e⟩ := hle f.2
  rwa [← Subtype.ext e]

end GlobalTheory.Branching
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
noncomputable section

namespace GlobalTheory.Cmp.JumpDict

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Cmp.SmallJumps

section Split

variable {Qp K LL M : Type} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
  [AddCommGroup M] [Module LL M] [Module Qp M] [IsScalarTower Qp LL M] [FiniteDimensional Qp K]

theorem finrank_eq_sum_emb (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (m : K →ₐ[Qp] Module.End LL M) (U : Submodule LL M) (hU : ∀ c, ∀ x ∈ U, m c x ∈ U)
    (E : (K →ₐ[Qp] LL) → Submodule LL M) (hE : ∀ τ x, x ∈ E τ ↔ x ∈ U ∧ ∀ c, m c x = τ c • x)
    [∀ τ, FiniteDimensional LL (E τ)] : finrank LL U = ∑ τ, finrank LL (E τ) := by
  classical
  let Φ : LL ⊗[Qp] K →ₐ[LL] ((K →ₐ[Qp] LL) → LL) :=
    Pi.algHom _ _ fun τ => Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => Commute.all _ _
  have hΦ : ∀ (a : LL) (c : K) τ, Φ (a ⊗ₜ c) τ = a * τ c := fun a c τ => by simp [Φ]
  have hsurj : Function.Surjective Φ := by
    have hli : LinearIndependent LL (fun τ : K →ₐ[Qp] LL => (τ : K → LL)) :=
      (linearIndependent_monoidHom K LL).comp (fun τ : K →ₐ[Qp] LL => (τ : K →* LL))
        (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range Φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ c, funext fun τ => by simp [hΦ, flip]⟩
    exact LinearMap.range_eq_top.1 this
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap) (by
      simp [hcard])).2 hsurj
  let Ψ : LL ⊗[Qp] K →ₐ[LL] Module.End LL M :=
    Algebra.TensorProduct.lift (Algebra.ofId LL _) m fun a c => Algebra.commutes a (m c)
  have hΨ : ∀ (a : LL) (c : K) x, Ψ (a ⊗ₜ c) x = a • m c x := fun a c x =>
    (LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId LL _) m
      (fun a c => Algebra.commutes a (m c)) a c) x).trans (by simp)
  have hΨU : ∀ z, ∀ x ∈ U, Ψ z x ∈ U := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact U.smul_mem _ (hU c x hx)
    | add y z hy hz => rw [map_add (f := _)]; exact U.add_mem hy hz
  have hΨE : ∀ τ z, ∀ x ∈ E τ, Ψ z x = Φ z τ • x := by
    intro τ z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, hΦ, ((hE τ x).1 hx).2 c, smul_smul]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, hy, hz, add_smul]
  choose e he using fun τ : K →ₐ[Qp] LL => hsurj (Pi.single τ 1)
  have he1 : ∑ τ, e τ = 1 := hinj (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : LL)))
  have he2 : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := fun τ c => hinj (by
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [hΦ]
    · simp [h])
  have hmem : ∀ τ, ∀ x ∈ U, Ψ (e τ) x ∈ E τ := fun τ x hx =>
    (hE τ _).2 ⟨hΨU _ x hx, fun c => by
      have := congrArg (fun z => Ψ z x) (he2 τ c)
      simpa only [map_mul, map_smul, Module.End.mul_apply, hΨ, one_smul, LinearMap.smul_apply] using this⟩
  let f : U ≃ₗ[LL] (∀ τ, E τ) :=
    { toFun := fun x τ => ⟨Ψ (e τ) x, hmem τ x x.2⟩
      map_add' := fun x y => funext fun τ => Subtype.ext (by simp)
      map_smul' := fun a x => funext fun τ => Subtype.ext (by simp)
      invFun := fun y => ⟨∑ τ, (y τ : M), U.sum_mem fun τ _ => ((hE τ _).1 (y τ).2).1⟩
      left_inv := fun x => Subtype.ext (by
        change ∑ τ, Ψ (e τ) x = x
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← LinearMap.sum_apply, ← map_sum, he1, map_one, Module.End.one_apply])
      right_inv := fun y => funext fun τ => Subtype.ext (by
        change Ψ (e τ) (∑ σ, (y σ : M)) = y τ
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single τ]
        · rw [hΨE τ _ _ (y τ).2, he]; simp
        · intro σ _ h
          rw [hΨE σ _ _ (y σ).2, he]; simp [h]
        · simp) }
  rw [f.finrank_eq, Module.finrank_pi_fintype]

end Split

theorem finrank_eq_one_of_jump {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) [FiniteDimensional L U] (le : ∀ a, F a ≤ U) (anti : ∀ a, F (a + 1) ≤ F a)
    (exh : ∀ x ∈ U, ∃ a, x ∈ F a) (sep : ∀ x, (∀ a, x ∈ F a) → x = 0) (a₀ : ℤ)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = if a = a₀ then 1 else 0) :
    finrank L U = 1 := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  haveI : ∀ a, FiniteDimensional L (F a) := fun a => Submodule.finiteDimensional_of_le (le a)
  have hs : ∀ a, a ≠ a₀ → F (a + 1) = F a := fun a ha =>
    Submodule.eq_of_le_of_finrank_eq (anti a) (by have := h a; rw [if_neg ha] at this; omega)
  have hlo : ∀ a ≤ a₀, F a = F a₀ := by
    intro a ha
    induction a, ha using Int.leInductionDown with
    | base => rfl
    | pred a ha ih => rw [← ih, ← hs (a - 1) (by omega), sub_add_cancel]
  have hhi : ∀ a, a₀ + 1 ≤ a → F a = F (a₀ + 1) := by
    intro a ha
    induction a, ha using Int.leInduction with
    | base => rfl
    | succ a ha ih => rw [← ih, hs a (by omega)]
  have h1 : U = F a₀ := le_antisymm (fun x hx => by
    obtain ⟨a, ha⟩ := exh x hx
    rcases le_total a a₀ with hab | hab
    · rwa [← hlo a hab]
    · exact hA hab ha) (le _)
  have h2 : F (a₀ + 1) = ⊥ := eq_bot_iff.2 fun x hx => sep x fun a => by
    rcases le_total a (a₀ + 1) with hab | hab
    · exact hA hab hx
    · rwa [hhi a hab]
  have h3 := h a₀
  rw [h2, if_pos rfl, finrank_bot] at h3
  rw [h1]
  omega

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := BdR) b).injective
  rw [map_zero]
  ext i
  refine PD.Fil_sep _ fun a => ?_
  obtain ⟨y, rfl⟩ := hx a
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    have : (equivFinsuppOfBasisLeft (N := BdR) b) (v ⊗ₜ (c : BdR)) i ∈ PD.Fil a := by
      rw [equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ c.2
    exact this
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]; exact Submodule.add_mem _ hy hz

theorem finrank_ddR_of_one_jump [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V)
    (h : ∀ τ : K →ₐ[Qp] LL, ∃ a₀ : ℤ, ∀ a, multV PD ρ τ a = if a = a₀ then 1 else 0) :
    finrank LL (DdR PD ρ) = finrank Qp K := by
  choose a₀ h using h
  haveI : ∀ τ, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    finite_ddRE_of_multV PD ρ τ {a₀ τ} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have h1 : ∀ τ, finrank LL (DdRE PD ρ τ) = 1 := fun τ =>
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left)
      (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) (a₀ τ) (h τ)
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [finrank_eq_sum_emb hcard m (DdR PD ρ) (fun c x hx => (hD _).2 fun g => by rw [hc, (hD x).1 hx g])
    (DdRE PD ρ) (fun τ x => by
      simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rfl)]
  simp [h1, hcard]

end Periods

variable (D : D7)

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Local

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.Cmp.JumpDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open scoped TensorProduct

namespace GlobalTheory.TwistedSelmerCompare

theorem natCast_mem_maximalIdeal {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _
  have h2 := IsLocalRing.eq_maximalIdeal h
  have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h2, Ideal.mem_comap, map_natCast] at h3
  exact h3

theorem padicInt_hom_ext {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (f g : ℤ_[l] →+* O) : f = g := by
  ext z
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  have : f z - g z = (f c - g c) * (l : O) ^ n := by
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl n)

theorem crystallineCocycle_transport_conjugation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K₁ K₂ L₁ L₂ : FinExt l)
    (θ : ↥(GK K₂) →* ↥(GK K₁)) (hθ : Continuous θ) (σ : GQ l)
    (hσ : ∀ g : ↥(GK K₂), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹) {k : ℕ}
    (M₁ : ↥(GK K₁) →* Matrix (Fin k) (Fin k) ↥L₁.1) (M₂ : ↥(GK K₂) →* Matrix (Fin k) (Fin k) ↥L₂.1)
    (p : ↥L₁.1 →ₗ[ℚ_[l]] ↥L₂.1)
    (hp : ∀ g (v : Fin k → ↥L₁.1), (fun j => p ((M₁ (θ g)).mulVec v j)) = (M₂ g).mulVec fun j => p (v j))
    (c : ↥(GK K₁) → Fin k → ↥L₁.1) (hc : c ∈ finiteCocycles (P.PD K₁) (matRep M₁)) :
    (fun g j => p (c (θ g) j)) ∈ finiteCocycles (P.PD K₂) (matRep M₂) := by
  obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hc
  have := L₁.2
  have hpc : Continuous p := p.continuous_of_finiteDimensional
  let q : (Fin k → ↥L₁.1) →ₗ[ℚ_[l]] (Fin k → ↥L₂.1) := LinearMap.compLeft p (Fin k)
  have hq : ∀ g v, q (matRep M₁ (θ g) v) = matRep M₂ g (q v) := fun g v => hp g v
  let T := TensorProduct.map q (P.actQ σ).toLinearMap
  have hT : ∀ g y, T (actVB (P.PD K₁) (matRep M₁) (θ g) y) = actVB (P.PD K₂) (matRep M₂) g (T y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b =>
      change q (matRep M₁ (θ g) v) ⊗ₜ[ℚ_[l]] P.actQ σ ((P.PD K₁).actB (θ g) b) =
        matRep M₂ g (q v) ⊗ₜ[ℚ_[l]] (P.PD K₂).actB g (P.actQ σ b)
      rw [hq, P.PD_actB, P.PD_actB, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul]
      congr 3
      rw [hσ g]; group
  refine ⟨⟨continuous_pi fun j => hpc.comp ((continuous_apply j).comp (hc1.comp hθ)), fun g h => ?_⟩,
    T x, fun g => ?_⟩
  · change q (c (θ (g * h))) = q (c (θ g)) + matRep M₂ g (q (c (θ h)))
    rw [map_mul, hc2, map_add (f := _), hq]
  · rw [← hT, ← map_sub, ← hx]
    change q (c (θ g)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = q (c (θ g)) ⊗ₜ[ℚ_[l]] P.actQ σ 1
    rw [map_one]

section Coef

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem toLLK_bijective (B : LocBridge l E Ω Gw O) : Function.Bijective (Br.toLLK B) := by
  refine ⟨(Br.toLLK B).injective, fun x => ?_⟩
  have := B.LL.2
  have : Algebra.IsAlgebraic ℤ_[l] ↥B.LL.1 := IsFractionRing.comap_isAlgebraic_iff.2
    (inferInstance : Algebra.IsAlgebraic ℚ_[l] ↥B.LL.1)
  obtain ⟨d, hd, hx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
  obtain ⟨n, hn⟩ := B.eO.surjective ⟨d • x, hx⟩
  refine ⟨algebraMap O _ n / algebraMap O _ (algebraMap ℤ_[l] O d), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, hn, B.eO_alg, ← IsScalarTower.algebraMap_apply, div_eq_iff]
  · change d • x = _
    rw [Algebra.smul_def, mul_comm]
  · rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥B.LL.1]
    simpa using hd

theorem exists_coefMap (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (f : O₀ →+* O)
    (hf : Function.Injective f) (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ φ : ↥B₀.LL.1 →ₐ[ℚ_[l]] ↥B.LL.1,
      ∀ x : FractionRing O₀, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := by
  let e := RingEquiv.ofBijective _ (toLLK_bijective B₀)
  let φ : ↥B₀.LL.1 →+* ↥B.LL.1 := (Br.toLLK B).comp ((GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf).comp e.symm.toRingHom)
  have hφ : ∀ x, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := fun x =>
    congrArg (fun y => Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf y)) (e.symm_apply_apply x)
  have hc : φ.comp (algebraMap ℚ_[l] ↥B₀.LL.1) = algebraMap ℚ_[l] ↥B.LL.1 := by
    refine IsFractionRing.ringHom_ext (A := ℤ_[l]) fun z => ?_
    have h := hφ (algebraMap O₀ _ (algebraMap ℤ_[l] O₀ z))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, hz, Br.toLLK_alg, Br.toLLK_alg, B.eO_alg, B₀.eO_alg,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  exact ⟨{ φ with commutes' := fun q => DFunLike.congr_fun hc q }, hφ⟩

end Coef

end GlobalTheory.TwistedSelmerCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsFurther
namespace GlobalTheory.DeterminantSimpLemma

open NumberField

theorem main {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [← hab, map_mul]
      field_simp
    rw [key]
    exact M.smul_mem _ h

end GlobalTheory.DeterminantSimpLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualLat

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_mem_one [StarRing K] {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) :
    star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

theorem exists_den_finset (s : Finset K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ s, d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s
  exact ⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩

theorem exists_smul_mem {M : Submodule (𝓞 K) (Fin n → K)}
    {x : Fin n → K} (hx : x ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.DeterminantSimpLemma.main
  | exact _root_.GlobalTheory.DeterminantSimpLemma.main
  | (apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantSimpLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantSimpLemma.main ..)

theorem isLattice_dualFr (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsFullLattice K M) :
    Submodule.IsFullLattice K (dualFr M) :=
  du_dualFr_lattice latticeBasisExists_holds M hM

theorem isLattice_hdualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (hdualFr G M) :=
  (dualFrameLattice_holds K n G M hG hM).2

omit [NumberField K] in
theorem star_dot [StarRing K] (x y : Fin n → K) : star (x ⬝ᵥ y) = star y ⬝ᵥ star x := by
  simp [dotProduct, mul_comm]

theorem hdualFr_dualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) : hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M) := by
  have key : ∀ φ ψ : Fin n → K, star φ ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ψ) = ψ ⬝ᵥ (G⁻¹ *ᵥ star φ) := by
    intro φ ψ
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  ext ψ
  constructor
  · intro h x hx
    have hφ : star (G *ᵥ x) ∈ dualFr M := by
      intro y hy
      have := star_mem_one (hx y hy)
      rwa [star_dot, star_star] at this
    have := h _ hφ
    rwa [key, star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec] at this
  · intro h φ hφ
    rw [key]
    refine h _ fun y hy => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec, ← star_dot]
    exact star_mem_one (hφ y hy)

theorem dualFr_lattice_and_hdual :
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
      (M : Submodule (𝓞 K) (Fin n → K)), IsUnit G.det → Submodule.IsFullLattice K M →
      Submodule.IsFullLattice K (dualFr M) ∧ Submodule.IsFullLattice K (hdualFr G M)) ∧ DualFrHdual :=
  ⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩,
    fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩

end GlobalTheory.DualLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_isLattice_and_hermitianDual : DualFrLattice ∧ DualFrHdual := by
  first | exact @GlobalTheory.DualLat.dualFr_lattice_and_hdual | exact GlobalTheory.DualLat.dualFr_lattice_and_hdual | (intros; apply GlobalTheory.DualLat.dualFr_lattice_and_hdual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight
open GlobalTheory.DualWeyl MvPolynomial NumberField Formalism.GradedWeylDivisibility

namespace GlobalTheory.DualWeyl

theorem rowDeg_dominated_of_mem_nabla {K : Type} [Field K] {N : ℕ} (la : Fin N → ℕ) (f : Pol N K)
    (hf : f ∈ nabla la K) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, la t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, la t := by
  classical
  unfold nabla at hf
  rw [standardMonomialSpanDomain K N N la] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance K N N k sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem eq_evalAt_one_smul_extremal_of_rowWeight (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ)
    (hla : Antitone la) (f : Pol N K) (hf : f ∈ nabla la K)
    (hw' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la) : f = evalAt 1 f • extremal la K := by
  obtain ⟨c, hc⟩ : ∃ c : K, f = c • extremal la K := by
    apply hwLine K N N le_rfl la hla f hf
    intro a b hab k hk
    by_contra hne
    have hmem := rowDivStable K N N la a b k f hf
    have hht : IsWeightedHomogeneous (lhwinHt N N) f (∑ a : Fin N, (a.val : ℤ) * (la a : ℤ)) := by
      intro d hd
      rw [lhwin_weight_ht, hw' hd]
    have hsh := lhwin_rowDiv_shift K _ a b k f hht
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    have e := hsh hd
    rw [lhwin_weight_ht] at e
    simp only [ldrow_weight_rowW] at e
    have dom := rowDeg_dominated_of_mem_nabla la _ hmem d (mem_support_iff.mpr hd)
    have hle := Formalism.BranchingDeterminantCap.bs_height_le N (rowDeg d) la dom.1 dom.2
    have hab' : (a.val : ℤ) - b.val ≤ -1 := by
      have : a.val < b.val := hab
      omega
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h1 : evalAt 1 f = c := by
    rw [hc, map_smul, evalAt_one_extremal, smul_eq_mul, mul_one]
  rw [h1]
  exact hc

end GlobalTheory.DualWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeightStatement
open GlobalTheory.DualWeyl MvPolynomial NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ), Antitone la → ∀ f ∈ nabla la K, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la → f = evalAt 1 f • extremal la K := by
  first | exact @GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | exact GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | (intros; apply GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem zpow_mul_eq_iff_toNat (d x y : ℂ) (hd : d ≠ 0) (a b : ℤ) :
    d ^ a * x = d ^ b * y ↔ d ^ (a - b).toNat * x = d ^ (b - a).toNat * y := by
  have ha : d ^ a = d ^ (min a b) * d ^ (a - b).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  have hb : d ^ b = d ^ (min a b) * d ^ (b - a).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  rw [ha, hb, mul_assoc, mul_assoc, mul_right_inj' (zpow_ne_zero _ hd)]

theorem exists_coef_sqRep (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu)
    (l : Module.Dual ℂ (nablaSq ℂ n mu)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      l (sqRep ℂ n mu g f) = (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift *
        eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2) P := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend l
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.1 n n f L
  refine ⟨rename Prod.swap P, fun g => ?_⟩
  rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, sqRep_coe, sqAct, map_smul, hP, eval_rename]
  simp only [detPow, smul_eq_mul, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem intertwining_gl_of_unitary (n : ℕ) (mu nu : DomWeight n)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu))
    (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu) :
    φ (sqRep ℂ n mu g f) = sqRep ℂ n nu g (φ f) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P, hP⟩ := exists_coef_sqRep n mu f (l ∘ₗ φ.toLinearMap)
  obtain ⟨Q, hQ⟩ := exists_coef_sqRep n nu (φ f) l
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  have hD : ∀ m : Matrix (Fin n) (Fin n) ℂ, eval (fun x => m x.1 x.2) D = m.det := by
    intro m
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  have key : ∀ g : GL (Fin n) ℂ, l (φ (sqRep ℂ n mu g f)) = l (sqRep ℂ n nu g (φ f)) ↔
      eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2)
        (D ^ (mu.detShift - nu.detShift).toNat * P - D ^ (nu.detShift - mu.detShift).toNat * Q) = 0 := by
    intro g
    have h1 : l (φ (sqRep ℂ n mu g f)) = _ := hP g
    rw [h1, hQ, zpow_mul_eq_iff_toNat _ _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
    simp only [map_sub, map_mul, map_pow, hD, sub_eq_zero]
  have hz := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.2 n _ fun u hu =>
    (key (unitaryIncl n ⟨u, hu⟩)).1 (congrArg l (φ.isIntertwining _ _ ⟨u, hu⟩ f))
  rw [key, hz, map_zero]

end GlobalTheory.Branching
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  apply SetLike.ext
  intro φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
end

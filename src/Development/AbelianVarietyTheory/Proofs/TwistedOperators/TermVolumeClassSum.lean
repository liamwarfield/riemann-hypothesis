module

public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsTest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSummandEmbeddingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEquivEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.BranchMultOne

instance fintypeSsIdx {n : ℕ} (ν : Fin n → ℕ) : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) :=
  @Fintype.ofFinite _ (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).to_subtype

def bSq {n : ℕ} (lam : DomWeight n) : Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) ℂ (nablaSq ℂ n lam) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW).choose_spec.1.2.1)

theorem bSq_coe {n : ℕ} (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ((bSq lam k : nablaSq ℂ n lam) : MvPolynomial (Fin n × Fin n) ℂ) = ssB ℂ lam.natW k := by
  simp [bSq, Module.Basis.span_apply, ssB]
  rfl

theorem ssB_mem {n : ℕ} (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ssB ℂ lam.natW k ∈ nablaSq ℂ n lam := bSq_coe lam k ▸ (bSq lam k).2

theorem sqAct_one_of_mem {n : ℕ} (lam : DomWeight n) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ∈ nablaSq ℂ n lam) :
    sqAct ℂ n lam 1 f = f := by
  have h := LinearMap.congr_fun (GlobalTheory.Branching.sqRep ℂ n lam).map_one ⟨f, hf⟩
  exact congrArg Subtype.val h

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tenAt {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ₀ : ι) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] Pol ℂ ι n :=
  LinearMap.mulLeft ℂ (∏ τ ∈ Finset.univ.erase τ₀, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) ∘ₗ
    (Formalism.GradedWeylDivisibility.blockEmb ℂ (k := n) (n := n) τ₀).toLinearMap

theorem tenAt_apply {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ₀ : ι) (x : MvPolynomial (Fin n × Fin n) ℂ) :
    tenAt f τ₀ x = ten (Function.update f τ₀ x) := by
  simp only [tenAt, ten, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

def partCoord {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) : VV ℂ lam →ₗ[ℂ] nablaSq ℂ n (lam τ₀) :=
  ∑ l, ((bVV ℂ lam).coord (Function.update j τ₀ l)).smulRight (bSq (lam τ₀) l)

theorem repr_partCoord {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) (v : VV ℂ lam) (l) :
    (bSq (lam τ₀)).repr (partCoord lam τ₀ j v) l = (bVV ℂ lam).repr v (Function.update j τ₀ l) := by
  have : partCoord lam τ₀ j v = ∑ l, (bVV ℂ lam).repr v (Function.update j τ₀ l) • bSq (lam τ₀) l := by
    simp [partCoord, LinearMap.sum_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem partCoord_bVV {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j j' : VVIdx lam) :
    partCoord lam τ₀ j (bVV ℂ lam j') = if (∀ τ, τ ≠ τ₀ → j' τ = j τ) then bSq (lam τ₀) (j' τ₀) else 0 := by
  simp only [partCoord, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with hc
  · have hj : j' = Function.update j τ₀ (j' τ₀) := by
      funext τ
      by_cases h : τ = τ₀
      · subst h; simp
      · rw [Function.update_of_ne h, hc τ h]
    rw [Finset.sum_eq_single (j' τ₀)]
    · rw [← hj]; simp
    · intro l _ hl
      rw [if_neg, zero_smul]
      intro e
      apply hl
      have := congrFun e τ₀
      simpa using this.symm
    · simp
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg, zero_smul]
    intro e
    apply hc
    intro τ h
    rw [e, Function.update_of_ne h]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem rhoK_update_bVV {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (g : GL (Fin n) ℂ) (j : VVIdx lam) :
    rhoK lam (Function.update 1 τ₀ g) (bVV ℂ lam j) =
      ∑ l, (bSq (lam τ₀)).repr (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀))) l •
        bVV ℂ lam (Function.update j τ₀ l) := by
  apply Subtype.ext
  rw [rhoK_coe, bVV_coe, bVVfun, actTen ℂ ι n lam _ _]
  have e1 : (fun τ => sqAct ℂ n (lam τ) (Function.update (1 : ι → GL (Fin n) ℂ) τ₀ g τ) (ssB ℂ (lam τ).natW (j τ))) =
      Function.update (fun τ => ssB ℂ (lam τ).natW (j τ)) τ₀ (sqAct ℂ n (lam τ₀) g (ssB ℂ (lam τ₀).natW (j τ₀))) := by
    funext τ
    by_cases h : τ = τ₀
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h]; exact sqAct_one_of_mem _ (ssB_mem _ _)
  rw [e1, ← tenAt_apply]
  have e2 : sqAct ℂ n (lam τ₀) g (ssB ℂ (lam τ₀).natW (j τ₀)) = ∑ l, (bSq (lam τ₀)).repr
      (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀))) l • ssB ℂ (lam τ₀).natW l := by
    have h := (bSq (lam τ₀)).sum_repr (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀)))
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul, bSq_coe, GlobalTheory.Branching.sqRep_coe] at h2
    exact h2.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Submodule.coe_smul, bVV_coe, bVVfun, tenAt_apply]
  congr 2
  funext τ
  exact (Function.apply_update (fun τ k => ssB ℂ (lam τ).natW k) j τ₀ l τ).symm

theorem partCoord_rhoK {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) (g : GL (Fin n) ℂ) (v : VV ℂ lam) :
    partCoord lam τ₀ j (rhoK lam (Function.update 1 τ₀ g) v) =
      GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (partCoord lam τ₀ j v) := by
  have key : partCoord lam τ₀ j ∘ₗ rhoK lam (Function.update 1 τ₀ g) =
      GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g ∘ₗ partCoord lam τ₀ j := by
    refine (bVV ℂ lam).ext fun j' => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, rhoK_update_bVV, map_sum, map_smul, partCoord_bVV]
    have hc : ∀ l, ((∀ τ, τ ≠ τ₀ → Function.update j' τ₀ l τ = j τ) ↔ (∀ τ, τ ≠ τ₀ → j' τ = j τ)) := fun l =>
      forall_congr' fun τ => imp_congr_right fun h => by rw [Function.update_of_ne h]
    by_cases h : ∀ τ, τ ≠ τ₀ → j' τ = j τ
    · rw [if_pos h]
      have e : ∀ l, (if (∀ τ, τ ≠ τ₀ → Function.update j' τ₀ l τ = j τ) then
          bSq (lam τ₀) (Function.update j' τ₀ l τ₀) else 0) = bSq (lam τ₀) l := fun l => by
        rw [if_pos ((hc l).2 h), Function.update_self]
      simp only [e]
      exact (bSq (lam τ₀)).sum_repr _
    · rw [if_neg h, map_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (fun h' => h ((hc l).1 h')), smul_zero]
  exact LinearMap.congr_fun key v

def factorIncl {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) : nablaSq ℂ n (lam τ₀) →ₗ[ℂ] VV ℂ lam :=
  LinearMap.codRestrict (VV ℂ lam) (tenAt (fun τ => ssB ℂ (lam τ).natW (i τ)) τ₀ ∘ₗ (nablaSq ℂ n (lam τ₀)).subtype)
    fun x => by
      rw [LinearMap.comp_apply, tenAt_apply]
      refine GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => ?_
      by_cases h : τ = τ₀
      · subst h; simpa using x.2
      · rw [Function.update_of_ne h]; exact ssB_mem _ _

theorem factorIncl_coe {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (x : nablaSq ℂ n (lam τ₀)) :
    (factorIncl lam τ₀ i x : Pol ℂ ι n) = ten (Function.update (fun τ => ssB ℂ (lam τ).natW (i τ)) τ₀ (x : MvPolynomial (Fin n × Fin n) ℂ)) := by
  simp [factorIncl, tenAt_apply]

theorem factorIncl_bSq {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (k) :
    factorIncl lam τ₀ i (bSq (lam τ₀) k) = bVV ℂ lam (Function.update i τ₀ k) := by
  apply Subtype.ext
  rw [factorIncl_coe, bSq_coe, bVV_coe, bVVfun]
  congr 1
  funext τ
  exact (Function.apply_update (fun τ k => ssB ℂ (lam τ).natW k) i τ₀ k τ).symm

theorem factorIncl_sqRep {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (G : GL (Fin n) ℂ) (x : nablaSq ℂ n (lam τ₀)) :
    factorIncl lam τ₀ i (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) G x) = rhoK lam (Function.update 1 τ₀ G) (factorIncl lam τ₀ i x) := by
  apply Subtype.ext
  rw [rhoK_coe, factorIncl_coe, factorIncl_coe, actTen ℂ ι n lam _ _]
  congr 1
  funext τ
  by_cases h : τ = τ₀
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h, Pi.one_apply,
      sqAct_one_of_mem _ (ssB_mem _ _)]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_mul_prod_of_slices {X : ι → Type} (m : ∀ τ, X τ → ℂ) (M : (∀ τ, X τ) → ℂ)
    (h : ∀ τ ω, ∃ c, ∀ x, M (Function.update ω τ x) = c * m τ x) :
    ∃ C, ∀ ω, M ω = C * ∏ τ, m τ (ω τ) := by
  by_cases hz : ∃ τ, ∀ x, m τ x = 0
  · obtain ⟨τ, hτ⟩ := hz
    refine ⟨0, fun ω => ?_⟩
    obtain ⟨c, hc⟩ := h τ ω
    have := hc (ω τ)
    rw [Function.update_eq_self, hτ, mul_zero] at this
    rw [this, zero_mul]
  push_neg at hz
  choose xs hxs using hz
  have hP : (∏ τ, m τ (xs τ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hxs τ
  have hp : ∀ (ω : ∀ τ, X τ) (a : ι) (y : X a),
      ∏ τ, m τ (Function.update ω a y τ) = m a y * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
    intro ω a y
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ hτ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
  refine ⟨M xs / ∏ τ, m τ (xs τ), ?_⟩
  suffices H : ∀ s : Finset ι, ∀ ω : (∀ τ, X τ), (∀ τ, τ ∉ s → ω τ = xs τ) →
      M ω = M xs / (∏ τ, m τ (xs τ)) * ∏ τ, m τ (ω τ) from fun ω => H Finset.univ ω (by simp)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro ω hω
    have : ω = xs := funext fun τ => hω τ (by simp)
    subst this
    field_simp
  · intro a s ha ih ω hω
    have h1 : M (Function.update ω a (xs a)) =
        M xs / (∏ τ, m τ (xs τ)) * ∏ τ, m τ (Function.update ω a (xs a) τ) := ih _ fun τ hτ => by
      by_cases e : τ = a
      · subst e; simp
      · rw [Function.update_of_ne e]; exact hω τ (by simp [e, hτ])
    obtain ⟨c, hc⟩ := h a ω
    have h2 : M ω = c * m a (ω a) := by simpa using hc (ω a)
    have h3 := hc (xs a)
    rw [h1, hp] at h3
    have hω_eq : ∏ τ, m τ (ω τ) = m a (ω a) * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
      simpa using hp ω a (ω a)
    have hc' : c = M xs / (∏ τ, m τ (xs τ)) * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
      apply mul_right_cancel₀ (hxs a)
      rw [← h3]; ring
    rw [h2, hω_eq, hc']
    ring

variable {N n : ℕ}

def brOneRep (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) :
    (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm lam).IntertwiningMap
      (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) :=
  ⟨(GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg).restrict fun f _ => GlobalTheory.BranchFormula.brOne_mem hN lam sg f,
   fun g => LinearMap.ext fun f => Subtype.ext (GlobalTheory.BranchFormula.brOne_sqAct hN hI hS g f.2)⟩

theorem brOneRep_coe (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) (f : nablaSq ℂ N lam) :
    (((brOneRep hN lam sg hI hS).toLinearMap f : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) =
      GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg f := rfl

theorem brOneRep_ne_zero (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) : brOneRep hN lam sg hI hS ≠ 0 := by
  intro h0
  apply Formalism.L2.Ker.brStd_ne_zero (K := ℂ) hN (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => hI) (fun _ => hS)
  refine LinearMap.ext fun G => Subtype.ext ?_
  obtain ⟨f, hf, e⟩ := GlobalTheory.BranchFormula.exists_ten_unit G.2
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg f = 0 := by
    have := brOneRep_coe hN lam sg hI hS ⟨f, hf⟩
    rw [h0] at this
    exact this.symm
  rw [GlobalTheory.BranchFormula.tensor ℂ Unit N n hN _ _ (fun _ => hI) (fun _ => hS) (fun _ => f) G (fun _ => hf) e, hz]
  simp [ten]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ}

def brEntry (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) (l : Formalism.GradedWeylDivisibility.ssIdx n n sg.natW) (k : Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) : ℂ :=
  (bSq sg).repr ((brOneRep hN lam sg hI hS).toLinearMap (bSq lam k)) l

theorem brStd_bVV (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (hI : ∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) (i : VVIdx Λ) :
    Formalism.L2.Col.Br.brStd hN Λ σ (bVV ℂ Λ i) =
      ∑ j : VVIdx σ, (∏ τ, brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ) (j τ) (i τ)) • bVV ℂ σ j := by
  apply Subtype.ext
  rw [GlobalTheory.BranchFormula.tensor ℂ ι N n hN Λ σ hI hS (fun τ => ssB ℂ (Λ τ).natW (i τ)) _ (fun τ => ssB_mem _ _)
    (by rw [bVV_coe, bVVfun])]
  have e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (Λ τ) (σ τ) (ssB ℂ (Λ τ).natW (i τ)) =
      ∑ l, brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ) l (i τ) • ssB ℂ (σ τ).natW l := by
    intro τ
    have h := congrArg Subtype.val ((bSq (σ τ)).sum_repr ((brOneRep hN (Λ τ) (σ τ) (hI τ) (hS τ)).toLinearMap
      (bSq (Λ τ) (i τ))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, bSq_coe, brOneRep_coe] at h
    rw [← h]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ten, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun x _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

theorem resRep_id_apply {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (g : GL (Fin n) ℂ) (x : nablaSq ℂ N lam) :
    GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm lam g x =
      GlobalTheory.Branching.sqRep ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) x := rfl

theorem smallRep_id_apply {n : ℕ} (sg : DomWeight n) (g : GL (Fin n) ℂ) (x : nablaSq ℂ n sg) :
    GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg g x = GlobalTheory.Branching.sqRep ℂ n sg g x := rfl

theorem embGL_update {ι : Type} [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (τ₀ : ι) (g : GL (Fin n) ℂ) :
    (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (Function.update (1 : ι → GL (Fin n) ℂ) τ₀ g τ)) =
      Function.update (1 : ι → GL (Fin N) ℂ) τ₀ (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) := by
  funext τ
  by_cases h : τ = τ₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n →
    ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) →
    (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ,
    (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) =
      rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  intro ι _ N n hN _ Λ σ hI hS φ hφ
  classical
  let B : ∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (σ τ).natW → Formalism.GradedWeylDivisibility.ssIdx N N (Λ τ).natW → ℂ :=
    fun τ => brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ)
  let M : VVIdx σ → VVIdx Λ → ℂ := fun j i => (bVV ℂ σ).repr (φ (bVV ℂ Λ i)) j
  have hslice : ∀ τ₀ (j : VVIdx σ) (i : VVIdx Λ), ∃ c, ∀ l k,
      M (Function.update j τ₀ l) (Function.update i τ₀ k) = c * B τ₀ l k := by
    intro τ₀ j i
    let ψ0 : nablaSq ℂ N (Λ τ₀) →ₗ[ℂ] nablaSq ℂ n (σ τ₀) := partCoord σ τ₀ j ∘ₗ φ ∘ₗ factorIncl Λ τ₀ i
    have hψ : ∀ g, ψ0 ∘ₗ (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)) g =
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) g ∘ₗ ψ0 := fun g => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, smallRep_id_apply, ψ0]
      rw [resRep_id_apply hN, factorIncl_sqRep, ← partCoord_rhoK, ← hφ, embGL_update hN]
    let ψ : (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)).IntertwiningMap
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) := ⟨ψ0, hψ⟩
    have h1 := (GlobalTheory.Branching.comult_id n N hN.symm (Λ τ₀) (σ τ₀)).1
      ((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.interlace_iff hN _ _).1 (hI τ₀))
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ (brOneRep_ne_zero hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀))).1 h1 ψ
    refine ⟨c, fun l k => ?_⟩
    have h2 := congrArg (fun F : (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)).IntertwiningMap
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) =>
      (bSq (σ τ₀)).repr (F.toLinearMap (bSq (Λ τ₀) k)) l) hc
    change (bVV ℂ σ).repr (φ (bVV ℂ Λ (Function.update i τ₀ k))) (Function.update j τ₀ l) = c * brEntry hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀) l k
    rw [← repr_partCoord, ← factorIncl_bSq]
    change _ = (bSq (σ τ₀)).repr (ψ.toLinearMap (bSq (Λ τ₀) k)) l at h2
    have h3 : ((bSq (σ τ₀)).repr (partCoord σ τ₀ j (φ (factorIncl Λ τ₀ i (bSq (Λ τ₀) k))))) l =
        (bSq (σ τ₀)).repr (ψ.toLinearMap (bSq (Λ τ₀) k)) l := rfl
    rw [h3, ← h2]
    show (bSq (σ τ₀)).repr (c • ((brOneRep hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀)).toLinearMap (bSq (Λ τ₀) k))) l = _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨C, hC⟩ := eq_mul_prod_of_slices
    (X := fun τ => Formalism.GradedWeylDivisibility.ssIdx n n (σ τ).natW × Formalism.GradedWeylDivisibility.ssIdx N N (Λ τ).natW)
    (fun τ p => B τ p.1 p.2) (fun ω => M (fun τ => (ω τ).1) (fun τ => (ω τ).2)) (fun τ ω => by
      obtain ⟨c, hc⟩ := hslice τ (fun τ => (ω τ).1) (fun τ => (ω τ).2)
      refine ⟨c, fun x => ?_⟩
      have e1 : (fun τ' => (Function.update ω τ x τ').1) = Function.update (fun τ => (ω τ).1) τ x.1 :=
        funext fun τ' => Function.apply_update (fun _ p => p.1) ω τ x τ'
      have e2 : (fun τ' => (Function.update ω τ x τ').2) = Function.update (fun τ => (ω τ).2) τ x.2 :=
        funext fun τ' => Function.apply_update (fun _ p => p.2) ω τ x τ'
      show M (fun τ' => (Function.update ω τ x τ').1) (fun τ' => (Function.update ω τ x τ').2) = c * B τ x.1 x.2
      rw [e1, e2]
      exact hc x.1 x.2)
  refine ⟨C, (bVV ℂ Λ).ext fun i => (bVV ℂ σ).ext_elem fun j => ?_⟩
  have := hC (fun τ => (j τ, i τ))
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, brStd_bVV hN Λ σ hI hS i, Module.Basis.repr_sum_self,
    smul_eq_mul]
  exact this

end GlobalTheory.BranchMultOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariantStatement
open Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n → ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ, (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  first | exact @GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | exact GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | (intros; apply GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpac
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpac
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.Branching.Family

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem exists_poly_blockAct_coef {k : ℕ} (f : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (ι × Fin k × Fin k) ℂ)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → Matrix (Fin k) (Fin k) ℂ,
      l (Formalism.GradedWeylDivisibility.blockAct ℂ g f) = eval (fun x => g x.1 x.2.1 x.2.2) P := by
  classical

  let Φ : ι × Fin k × Fin k → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun v => ∑ b : Fin k, C (X (v.1, v.2.1, b) : MvPolynomial (ι × Fin k × Fin k) ℂ) * X (v.1, (b, v.2.2))
  let T : MvPolynomial (ι × Fin k × Fin k) ℂ → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun p => aeval Φ (map (C : ℂ →+* MvPolynomial (ι × Fin k × Fin k) ℂ) p)
  have hT : ∀ (g : ι → Matrix (Fin k) (Fin k) ℂ) (p : MvPolynomial (ι × Fin k × Fin k) ℂ),
      Formalism.GradedWeylDivisibility.blockAct ℂ g p = map (eval fun x => g x.1 x.2.1 x.2.2) (T p) := by
    intro g p
    induction p using MvPolynomial.induction_on with
    | C a => simp [T, aeval_C, MvPolynomial.algebraMap_eq, map_C, eval_C]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, T]
    | mul_X p v hp =>
      simp only [T] at hp ⊢
      simp only [map_mul, hp]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_X, Φ, map_sum, map_mul, map_C, eval_X]
  refine ⟨∑ m ∈ (T f).support, C (l (monomial m 1)) * (T f).coeff m, fun g => ?_⟩
  rw [hT g f]
  conv_lhs => rw [(T f).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, map_mul, eval_C]
  rw [show (monomial m (eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m)) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m) • monomial m 1 by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_coef_rhoK {k : ℕ} (lam : ι → DomWeight k) (f : VV ℂ lam) (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → GL (Fin k) ℂ,
      l (rhoK lam g f) = (∏ τ, (g τ : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift) *
        eval (fun x => (g x.1 : Matrix (Fin k) (Fin k) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (K := ℂ) (p := VV ℂ lam) l
  obtain ⟨P, hP⟩ := exists_poly_blockAct_coef (ι := ι) (k := k) (f : MvPolynomial (ι × Fin k × Fin k) ℂ) L
  refine ⟨rename (fun x : ι × Fin k × Fin k => (x.1, x.2.2, x.2.1)) P, fun g => ?_⟩
  have hl : l (rhoK lam g f) = L ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) := by
    rw [← hL]; rfl
  have hv : ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      detTwK lam g • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.transpose ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ))
        (f : MvPolynomial (ι × Fin k × Fin k) ℂ) := rfl
  have hd : detTwK lam g = ∏ τ, ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift := by
    simp only [detTwK, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [hl, hv, map_smul, hP, eval_rename, smul_eq_mul, hd]
  rfl

theorem det_diag_one {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g : Matrix (Fin N) (Fin N) ℂ).det = (g : Matrix (Fin n) (Fin n) ℂ).det := by
  subst h
  have h1 : ∀ a b : Fin n, ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) a.castSucc b.castSucc = (g : Matrix (Fin n) (Fin n) ℂ) a b := by
    intro a b
    simp [GlobalTheory.Branching.embGL_apply]
  have h2 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.Branching.embGL_apply]
  have hev : (-1 : ℂ) ^ (n + n) = 1 := Even.neg_one_pow ⟨n, rfl⟩
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp only [h2, Fin.succAbove_last, Fin.val_last, hev, one_mul, mul_one]
    congr 1
    ext a b
    exact h1 a b
  · intro j _ hj
    have h3 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) j = 0 := by
      simp [GlobalTheory.Branching.embGL_apply, Ne.symm hj]
    rw [h3, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_coef_rhoK_emb {n N : ℕ} (h : n + 1 = N) (lam : ι → DomWeight N) (f : VV ℂ lam)
    (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ g : ι → GL (Fin n) ℂ,
      l (rhoK lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h (g τ)) f) =
        (∏ τ, (g τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
          eval (fun x => (g x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨P, hP⟩ := exists_coef_rhoK lam f l

  let S : ι × Fin N × Fin N → MvPolynomial (ι × Fin n × Fin n) ℂ := fun x =>
    if hab : x.2.1.val < n ∧ x.2.2.val < n then X (x.1, ⟨x.2.1.val, hab.1⟩, ⟨x.2.2.val, hab.2⟩)
    else if x.2.1 = x.2.2 then 1 else 0
  refine ⟨aeval S P, fun g => ?_⟩
  rw [hP, Formalism.L2.Col.eval_aeval_poly]
  simp only [det_diag_one]
  congr 1
  apply congrArg (fun F => eval F P)
  funext x
  simp only [S, GlobalTheory.Branching.embGL_apply]
  split_ifs <;> simp

theorem prod_zpow_mul_eq_iff (d : ι → ℂ) (x y : ℂ) (hd : ∀ τ, d τ ≠ 0) (a b : ι → ℤ) :
    (∏ τ, d τ ^ a τ) * x = (∏ τ, d τ ^ b τ) * y ↔
      (∏ τ, d τ ^ (a τ - b τ).toNat) * x = (∏ τ, d τ ^ (b τ - a τ).toNat) * y := by

  have split : ∀ (c e : ι → ℤ) τ, d τ ^ c τ = d τ ^ min (c τ) (e τ) * d τ ^ (c τ - e τ).toNat := by
    intro c e τ
    rw [← zpow_natCast, ← zpow_add₀ (hd τ)]
    congr 1
    rcases le_total (c τ) (e τ) with h | h
    · have h' : c τ - e τ ≤ 0 := by linarith
      rw [min_eq_left h, Int.toNat_of_nonpos h', Nat.cast_zero, add_zero]
    · have h' : 0 ≤ c τ - e τ := by linarith
      rw [min_eq_right h, Int.toNat_of_nonneg h']
      ring
  have hne : (∏ τ, d τ ^ min (a τ) (b τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hd τ)
  have hmin : ∀ τ, min (b τ) (a τ) = min (a τ) (b τ) := fun τ => min_comm _ _
  rw [Finset.prod_congr rfl fun τ _ => split a b τ, Finset.prod_congr rfl fun τ _ => split b a τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [hmin]
  rw [mul_assoc, mul_assoc, mul_right_inj' hne]

theorem equivariant_gl_of_unitary {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) =
        rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v))
    (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ) :
    φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  classical
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P₁, hP₁⟩ := exists_coef_rhoK_emb hN.symm Λ v (l ∘ₗ φ)
  obtain ⟨P₂, hP₂⟩ := exists_coef_rhoK σ (φ v) l

  let D : ι → MvPolynomial (ι × Fin n × Fin n) ℂ := fun τ =>
    (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hD : ∀ (y : ι → Matrix (Fin n) (Fin n) ℂ) τ, eval (fun x => y x.1 x.2.1 x.2.2) (D τ) = (y τ).det := by
    intro y τ
    simp only [D]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [RingHom.mapMatrix_apply]
  let a : ι → ℤ := fun τ => (Λ τ).detShift
  let b : ι → ℤ := fun τ => (σ τ).detShift

  let Q := (∏ τ, D τ ^ (a τ - b τ).toNat) * P₁ - (∏ τ, D τ ^ (b τ - a τ).toNat) * P₂
  have hQ : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, eval (fun x => y x.1 x.2.1 x.2.2) Q =
      (∏ τ, (y τ).det ^ (a τ - b τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₁ -
        (∏ τ, (y τ).det ^ (b τ - a τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₂ := by
    intro y
    simp only [Q, map_sub, map_mul, map_prod, map_pow, hD]

  have hQ0 : Q = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (fun _ => 1) (fun _ => by simp) Q fun u hu => ?_
    simp only [one_mul]
    let w : ι → Matrix.unitaryGroup (Fin n) ℂ := fun τ =>
      ⟨u τ, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)⟩
    have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have e := congrArg l (hφ w v)
    have e₁ := hP₁ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    have e₂ := hP₂ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    simp only [LinearMap.comp_apply] at e₁
    rw [e₁, e₂] at e
    simp only [GlobalTheory.Branching.unitaryIncl_coe] at e
    rw [hQ u, sub_eq_zero]
    exact (prod_zpow_mul_eq_iff (fun τ => (u τ).det) _ _ hdet a b).mp e
  have hg : ∀ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := fun τ =>
    by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have e₃ := hQ (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ))
  rw [hQ0, map_zero, eq_comm, sub_eq_zero] at e₃
  have e₁ := hP₁ g
  simp only [LinearMap.comp_apply] at e₁
  rw [e₁, hP₂ g]
  exact (prod_zpow_mul_eq_iff (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det) _ _ hg a b).mpr e₃

end GlobalTheory.Branching.Family
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpacStatement
open Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ), (∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) = rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v)) → ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  first | exact @GlobalTheory.Branching.Family.equivariant_gl_of_unitary | exact GlobalTheory.Branching.Family.equivariant_gl_of_unitary | (intros; apply GlobalTheory.Branching.Family.equivariant_gl_of_unitary <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.BrUnique

variable {ι : Type} [Fintype ι] {N n : ℕ}

def uGL (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin n) ℂ := fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)

def diagU (hN : N = n + 1) (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin N) ℂ :=
  fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))

theorem invTrK_invTrK {K : Type} [Field K] (g : ι → GL (Fin n) K) : invTrK (invTrK g) = g := by
  funext τ
  apply Units.ext
  have hu : IsUnit ((g τ : Matrix (Fin n) (Fin n) K)).det := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
  simp [invTrK, inside₂, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]

theorem pairBK_rhoK (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ g x) (rhoK σ (invTrK g) y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  have h := pairingBInvariantK_holds ℂ ι n σ (invTrK g) x.1 y.1
  rwa [invTrK_invTrK] at h

theorem unitaryEquiv_eq_smul (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ)) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v)) :
    ∃ c : ℂ, φ = c • Br.brStd hN Λ σ :=
  GlobalTheory.T.exists_eq_smul_brStd_of_equivariant hN hn Λ σ hI hS φ (GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace hN Λ σ φ hφ)

theorem brPair_unique (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ))
    (B : VV ℂ Λ →ₗ[ℂ] (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] ℂ)
    (hB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ) (f : VV ℂ fun τ => (σ τ).dual),
      B (rhoK Λ (diagU hN u) v) (rhoK (fun τ => (σ τ).dual) (uGL u) f) = B v f) :
    ∃ c : ℂ, B = c • GlobalTheory.FunObj.brPair σ hN Λ := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  let φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ B.compl₂ (GlobalTheory.FunObj.funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (φ v) y = B v (GlobalTheory.FunObj.funEquiv σ y) := fun v y => by
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₂_apply]
  have hinv : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) v F,
      B (rhoK Λ (diagU hN u) v) F = B v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F) := fun u v F => by
    have h := hB u v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  have hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v) := fun u v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp, hinv]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK (uGL u)) y' :=
      ⟨rhoK σ (invTrK (uGL u))⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [pairBK_rhoK, hp, GlobalTheory.FunObj.funEquiv_rhoK, ← Module.End.mul_apply, ← map_mul, invTrK_invTrK, inv_mul_cancel,
      map_one, Module.End.one_apply]
  obtain ⟨c, hc⟩ := unitaryEquiv_eq_smul hN hn hI hS φ hφ
  refine ⟨c, LinearMap.ext₂ fun v f => ?_⟩
  have e : f = GlobalTheory.FunObj.funEquiv σ (GlobalTheory.FunObj.covOf σ f) := by rw [GlobalTheory.BrRat.covOf_eq, LinearEquiv.apply_symm_apply]
  rw [e, ← hp, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    ← e]
  simp only [GlobalTheory.FunObj.brPair, LinearMap.compl₁₂_apply]

end GlobalTheory.BrUnique
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add (f := _), add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add (f := _), mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))

variable (G) in
theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h

variable (G) in
theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)

variable (G) in
theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_left ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance

end

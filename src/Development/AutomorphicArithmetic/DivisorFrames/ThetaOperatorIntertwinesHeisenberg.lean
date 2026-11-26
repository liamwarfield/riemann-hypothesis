module

public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ThetaOperatorIntertwinesHeisenberg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem thetaSum_rho_rho' {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U]
    {B : U → U → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Φ : (κ → AF F) → ℂ) (x y : U) :
    GlobalTheory.WeilM.thetaSum F (co.rho ψ x (co.rho ψ y Φ)) =
      ψ (⅟(2 : AF F) * B x y) * GlobalTheory.WeilM.thetaSum F (co.rho ψ (x + y) Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho, schr_schr', GlobalTheory.WeilM.thetaSum, map_add (f := _), Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    co.form]

private theorem exists_co' {D : D7} {ε : Bool} {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank)
    {Vs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E d} (M : Model D.sp.cm.sig Vs Ws)
    (hX : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))) (Fin S.rank × Fin d),
      ∀ x, co.e x = M.co.e (ptO (sgn ε S).gram e x) := by
  have hdet : IsUnit (sgn ε S).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hG : ((sgn ε S).gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = ((sgn ε S).gram.map (incA D))ᵀ := by
    ext i j
    show cA D (incA D ((sgn ε S).gram i j)) = incA D ((sgn ε S).gram j i)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  have hVJ : Vs.J = -(sgn ε S).gram := by
    rw [hX]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G = (sgn ε S).gram := ⟨_, rfl⟩
  rw [← hGd] at hdet hG hVJ ⊢
  have h1 : G.map (incA D) * (G⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (G⁻¹).map (incA D) * G.map (incA D) = 1 := mul_eq_one_comm.1 h1
  have hp : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), ptO G e x = ((x * (G⁻¹).map (incA D))ᵀ).submatrix id e :=
    fun _ => rfl
  have hr : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), (ptO G e x)ᵀ.submatrix e.symm id * G.map (incA D) = x := fun x => by
    have e1 : (ptO G e x)ᵀ.submatrix e.symm id = x * (G⁻¹).map (incA D) := by
      rw [hp]
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [e1, Matrix.mul_assoc, h2, Matrix.mul_one]
  let T : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ Matrix (Fin X.rank) (Fin S.rank) (AE D) :=
    { toFun := fun u => uᵀ.submatrix e.symm id * G.map (incA D)
      invFun := ptO G e
      left_inv := fun u => by
        rw [hp, Matrix.mul_assoc, h1, Matrix.mul_one]
        ext i j
        simp only [submatrix_apply, transpose_apply, id, Equiv.symm_apply_apply]
      right_inv := hr
      map_add' := fun u v => by rw [← Matrix.add_mul]; rfl }
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) h2 hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • G⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _)
    (by rw [hW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co T (fun _ => rfl)
  exact ⟨co, fun x => (congrArg co.e (hr x)).symm.trans (hco _)⟩

theorem UpperTheory.thetaOperator_intertwines_heisenberg :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M →
        (∀ x y : WO (sgn ε S) X, GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (ptO (sgn ε S).gram e x) (ptO (sgn ε S).gram e y) =
          symplO (sgn ε S) X x y) ∧
        (∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (y : WO (sgn ε S) X),
          thO M ψ (sgn ε S).gram e (M.co.rho ψ (ptO (sgn ε S).gram e y) Φ) = heisO ψ (sgn ε S) X y (thO M ψ (sgn ε S).gram e Φ)) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e (Φ + Φ') = thO M ψ (sgn ε S).gram e Φ + thO M ψ (sgn ε S).gram e Φ') ∧
        (∀ (c : ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), thO M ψ (sgn ε S).gram e (c • Φ) = c • thO M ψ (sgn ε S).gram e Φ) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e Φ = thO M ψ (sgn ε S).gram e Φ' → Φ = Φ') ∧
        ∀ f : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f ↔
          ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), thO M ψ (sgn ε S).gram e Φ = f := by
  intro D ψ ε S X d e Bs Vs Ws M hP
  have hψ : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hP.psi ▸ hP.base.std)
  obtain ⟨co, hco⟩ := exists_co' e M hP.JV hP.JW
  have hr : ∀ x, co.rho ψ x = M.co.rho ψ (ptO (sgn ε S).gram e x) := fun x => by
    simp only [GlobalTheory.WeilM.Darboux.rho, hco]
  have hth : ∀ Φ, thO M ψ (sgn ε S).gram e Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := fun Φ => by
    funext x
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, hr]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hψ rfl (one_smul _ _) (fun x => by
    obtain ⟨y, z, h⟩ := hP.good.rat (((x * (sgn ε S).gram⁻¹)ᵀ).submatrix id e)
    refine ⟨y, z, Eq.trans ?_ h⟩
    rw [hco]
    congr 1
    exact (congrArg (fun m => (transpose m).submatrix id e) (Matrix.map_mul (f := incA D))).symm)
  have hs := GlobalTheory.ThetaTransform.symplO_eq_symp (S := sgn ε S) (T := X) (ξ := 1) rfl (one_smul _ _)
  simp only [hth]
  refine ⟨fun x y => ?_, fun Φ y => ?_, h1, GlobalTheory.ThetaTransform.thetaTr_smul co, h2, h3⟩
  · rw [hs, co.form, M.co.form, hco, hco]
  · funext x
    rw [← hr]
    show GlobalTheory.WeilM.thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) = _
    rw [thetaSum_rho_rho', ← hs, GlobalTheory.ThetaTransform.invOf_two_eq]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open Filter Topology ValuativeRel GlobalTheory.StdPairSB GlobalTheory.StdPairCone

private theorem gfun_lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h0 : ∀ e : ℕ, ∀ i j, (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ e) := by
    intro e i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
    simp
  have hfac : ∀ (A : Matrix (Fin m) (Fin m) k) (B : Matrix (Fin m) (Fin r) k),
      gfun ν ϖ c A B = if (∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) then
        gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) else 0 := by
    intro A B
    by_cases hB : ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
    · rw [if_pos hB]
      unfold gfun
      by_cases hA : A.det ≠ 0 ∧ IsGLO A
      · rw [dite_eq_left ⟨hA.1, hA.2, hB⟩, dite_eq_left ⟨hA.1, hA.2, h0 n⟩]
      · rw [dite_eq_right fun h => hA ⟨h.1, h.2.1⟩, dite_eq_right fun h => hA ⟨h.1, h.2.1⟩]
    · rw [if_neg hB]
      unfold gfun
      rw [dite_eq_right fun h => hB h.2.2]
  have h1 : IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        gfun ν ϖ n q.1 (0 : Matrix (Fin m) (Fin r) k)) :=
    (isLocallyConstant_gfun hϖ hν m r).comp_continuous
      (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ c))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      ∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).2 i j - B i j) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev, h1 (A, B)] with q hq hq1
  have hiff : (∀ i j, q.2 i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ↔
      ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    constructor
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_sub_cancel (q.2 i j) (B i j)]
      exact Valuation.map_sub_le _ (h i j) (hq i j)
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (q.2 i j) (B i j)]
      exact Valuation.map_add_le _ (hq i j) (h i j)
  show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
  rw [hfac, hfac]
  exact if_congr hiff hq1 rfl

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c a a' : ℕ) :
    stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
      stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j

end SlopeTestRemainingChoices

theorem UpperTheory.stdA_stdB_mem_schwartzBruhat :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∃ m, GlobalTheory.SplitFlip.CondLE ϖ m ν) → ∀ c a a' : ℕ,
        GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ hϖ hν c a a'
  obtain ⟨n, hn⟩ := hν
  exact finiteRing_sq_sub_mul_sq_eq_of_card ν ϖ hϖ hn c a a'
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section

open GlobalTheory.StdFrames (cpt comp_toAd)
open GlobalTheory.LFun (complMap)
open GlobalTheory.AdelicU (splitPrime_under)

variable {D : D7}

private theorem ext_cpt {a b : AE D} (h1 : infPart D a = infPart D b)
    (h2 : ∀ Q, cpt (D := D) Q (toEAf D a) = cpt (D := D) Q (toEAf D b)) : a = b :=
  (comp_toAd D).ext' h1 h2

private theorem cpt_base {Q : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : Q.under (𝓞 D.host.F) = v) (u : AF D.host.F) :
    cpt (D := D) Q (toEAf D (algebraMap _ (AE D) u)) = complMap h (evFin D.host.F v u) := by
  subst h
  exact (comp_toAd D).base u Q

private theorem cpt_split {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    cpt (D := D) (splitPrime τ) (toEAf D z) = complMap (splitPrime_under τ) (piW τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    have e1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap _ (AE D) a * incA D x := by
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : piW τ (a ⊗ₜ[D.host.F] x : AE D) = evFin D.host.F v a * τ x := rfl
    have e3 : cpt (D := D) (splitPrime τ) (toEAf D (incA D x)) = algebraMap _ _ x :=
      congrArg (fun s => s (splitPrime τ)) ((comp_toAd D).inc x)
    rw [e2, e1, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cpt_base (splitPrime_under τ), e3,
      GlobalTheory.LFun.SplitTie.complMap_apply_emb]

private theorem piW_comp {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piW (τ.comp D.sp.cm.sig) z = piW τ (cA D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

private theorem first_half {e₀ : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e₀ S)
    (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hP : ∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) (ht : ∀ v : P, splitPrime (t v) ∈ S) (z : AE D) :
    e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z := by
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  have one : ∀ {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ ∈ S →
      piW τ e₀ = 1 := fun τ h =>
    (complMap (splitPrime_under τ)).injective (by rw [← cpt_split, e1 _ h, RingHom.map_one])
  constructor
  · intro hz
    refine ⟨fun u hu => ?_, fun v => ?_⟩
    · have h0 : algebraMap _ (AE D) u * e₀ = 0 := by
        refine ext_cpt (by rw [RingHom.map_mul, e0, mul_zero, RingHom.map_zero]) fun Q => ?_
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_zero, RingHom.map_zero]
        by_cases hQ : Q ∈ S
        · rw [cpt_base rfl, hu _ ((hP _).2 ⟨Q, hQ, rfl⟩), RingHom.map_zero, zero_mul]
        · rw [e2 Q hQ, mul_zero]
      rw [Algebra.smul_def, ← hz, ← mul_assoc]
      exact (congrArg (· * z) h0).trans (zero_mul z)
    · have h0 := congrArg (piW (t v)) he.2
      rw [RingHom.map_mul, one _ (ht v), one_mul, RingHom.map_zero, ← piW_comp] at h0
      change piW ((t v).comp D.sp.cm.sig) z = 0
      rw [← hz, RingHom.map_mul, h0, zero_mul]
  · rintro ⟨h1, h2⟩
    have h1' : ∀ u : AF D.host.F, (∀ v ∈ P, evFin D.host.F v u = 0) → algebraMap _ (AE D) u * z = 0 :=
      fun u hu => (Algebra.smul_def u z).symm.trans (h1 u hu)
    refine ext_cpt ?_ fun Q => ?_
    · have h3 := congrArg (infPart D) (h1' ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) fun v _ => rfl)
      have h4 : infPart D (algebraMap (AF D.host.F) (AE D) ((1, 0) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) = 1 := rfl
      rw [RingHom.map_mul, h4, one_mul, RingHom.map_zero] at h3
      rw [RingHom.map_mul, h3, mul_zero]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hQ : Q ∈ S
      · rw [e1 Q hQ, one_mul]
      rw [e2 Q hQ, zero_mul, eq_comm]
      by_cases hv : Q.under (𝓞 D.host.F) ∈ P
      · have hm : Q.asIdeal ∈ (Q.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨rfl⟩⟩
        rw [GlobalTheory.AdelicU.primesOver_eq_split (GlobalTheory.AdelicU.isCMExt_host D) (t ⟨_, hv⟩)] at hm
        rcases hm with e | e
        · exact absurd ((HeightOneSpectrum.ext e : Q = _) ▸ ht ⟨_, hv⟩) hQ
        · have h5 := cpt_split ((t ⟨_, hv⟩).comp D.sp.cm.sig) z
          rw [h2 ⟨_, hv⟩, RingHom.map_zero] at h5
          have e' : Q = splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) := HeightOneSpectrum.ext e
          generalize splitPrime ((t ⟨_, hv⟩).comp D.sp.cm.sig) = Q' at h5 e'
          subst e'
          exact h5
      · let u : AF D.host.F := ((0, singleV D.host.F (Q.under (𝓞 D.host.F)) 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
        have h3 := congrArg (fun y => cpt (D := D) Q (toEAf D y)) (h1' u fun v hv' =>
          Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F)
            (fun e : v = Q.under (𝓞 D.host.F) => hv (e ▸ hv')) 1)
        have h4 : evFin D.host.F (Q.under (𝓞 D.host.F)) u = 1 :=
          Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) (Q.under (𝓞 D.host.F)) 1
        simp only [RingHom.map_mul, RingHom.map_zero] at h3
        rwa [cpt_base rfl, h4, RingHom.map_one, one_mul] at h3

private theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, GlobalTheory.IdemSupport.cA_algebraMap]

end

theorem UpperTheory.idempotentSum_fixes_iff_halfEl :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        (∀ z : AE D, e₀ * z = z ↔ HalfEl P (fun v => (t v).comp D.sp.cm.sig) z) ∧ ∀ z : AE D, cA D e₀ * z = z ↔ HalfEl P t z := by
  intro D e₀ S he P t hP ht
  refine ⟨first_half he P t hP ht, fun z => ?_⟩
  have hc : ∀ y : AE D, cA D (cA D y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (fun s => a ⊗ₜ[D.host.F] s) (star_star x)
  have hi : Function.Injective (cA D) := Function.LeftInverse.injective hc
  have h := first_half he P t hP ht (cA D z)
  rw [← hi.eq_iff, RingHom.map_mul, hc] at h
  refine h.trans (and_congr (forall_congr' fun u => imp_congr_right fun _ => ?_) (forall_congr' fun v => ?_))
  · change u • cA D z = 0 ↔ u • z = 0
    rw [← cA_smul, ← hi.eq_iff, hc, RingHom.map_zero]
  · change piW ((t v).comp D.sp.cm.sig) (cA D z) = 0 ↔ _
    rw [piW_comp, hc]
end

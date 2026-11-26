module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommute
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicHaarFiniteInfiniteProduct
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizer
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermRestrictSmoothModerate
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.StandardThreeBlockIndex
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCuspFunSlice
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermParabolicFiniteType
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CasimirAnnihilatedCuspFormsFiniteDimensional
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesGlPart

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

section General

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.UAut.ConstAut
open GlobalTheory.ThK.SmoothLev (IsSmModOn)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSmModOn_constTermOn (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {C : Matrix (Fin n) (Fin r) E}
    (d : Fin r → ℕ) (hC : IsIsoCols σ J C) {Γ : Set (GAd σ J)} {φ c : GAd σ J → ℂ}
    (hΓ : ((ratPts σ J ⊓ parFlag σ J C d : Subgroup (GAd σ J)) : Set (GAd σ J)) ⊆ Γ)
    (hφ : IsSmModOn σ J Γ φ) (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c) :
    IsSmModOn σ J (leftGrp σ J C d : Set (GAd σ J)) c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hs : IsSm σ J φ := hφ.smooth
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hΓ hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hs
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hs hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hsm : IsSm σ J c := by
    obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
    intro k γ hγ g
    have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
      (fun γ' hγ' x t => by simp only [mul_assoc]; exact hφΓ γ' hγ' _) (fun x => hs k γ hγ x)
      (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hs k γ hγ) g
    simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs'⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs' x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, hsm, hgrowth⟩, hct⟩

theorem depth_lt {r t : ℕ} (ht : t ≤ r) {T : Finset (Fin r)} {i j : Fin t} {k : Fin r} (hk : k ∈ T)
    (h1 : j.val ≤ k.val) (h2 : k.val < i.val) :
    (T.filter (· < Fin.castLE ht j)).card < (T.filter (· < Fin.castLE ht i)).card := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Fin.lt_def, Fin.val_castLE] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have h3 := hsub (Finset.mem_filter.2 ⟨hk, Fin.lt_def.2 (by simpa using h2)⟩)
    have h4 := Fin.lt_def.1 (Finset.mem_filter.1 h3).2
    simp only [Fin.val_castLE] at h4
    omega

theorem exists_block_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin t) (Fin t) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card)
    (e : M * adMat F (X.submatrix id (Fin.castLE ht)) = adMat F (X.submatrix id (Fin.castLE ht)) * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hst) (Fin.castLE hst), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (depth_lt ht (hST hk1.1) (i := Fin.castLE hst i) (j := Fin.castLE hst j) (by simpa using h1) (by simpa using h2))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hst j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F (X.submatrix id (Fin.castLE ht))) x (Fin.castLE hst j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hst) (Fin.castLE_injective hst) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    obtain ⟨k, hk, hjk⟩ := (hS (Fin.castLE hs j)).1 (by simp)
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    have hz : B i (Fin.castLE hst j) = 0 :=
      hB (depth_lt ht (hST hk) (by simpa [Fin.le_def] using hjk) (by omega))
    rw [hz, mul_zero]

theorem parFlag_le_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) :
    parFlag σ J (X.submatrix id (Fin.castLE ht)) (fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card) ≤
      parFlag σ J (X.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) :=
  fun _ ⟨⟨B, hB, e⟩, B', hB', e'⟩ =>
    ⟨exists_block_of_subset X hST hs ht hst hS hB e, exists_block_of_subset X hST hs ht hst hS hB' e'⟩

def top {r : ℕ} (S : Finset (Fin r)) : ℕ := S.sup fun k => k.val + 1

theorem top_le {r : ℕ} (S : Finset (Fin r)) : top S ≤ r := Finset.sup_le fun k _ => k.2

theorem top_mono {r : ℕ} {S T : Finset (Fin r)} (h : S ⊆ T) : top S ≤ top T := Finset.sup_mono h

theorem lt_top_iff {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : i.val < top S ↔ ∃ k ∈ S, i ≤ k := by
  rw [top, Finset.lt_sup_iff]
  exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega

theorem leftGrp_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) :
    leftGrp σ J (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) =
      GlobalTheory.StdPar.unip σ J X S ⊔ (ratPts σ J ⊓ GlobalTheory.StdPar.levi σ J X Y S) := by
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (top S) (top_le S) (lt_top_iff S)
    (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) fun _ => rfl
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ (top S) (X.submatrix id (Fin.castLE (top_le S)))
    (Y.submatrix id (Fin.castLE (top_le S))) (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective _))).2.2.1
  rw [hg, hu, hl]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem isSmModOn_constAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  intro D V m X Y hW S T hST _ φ c hφ hc
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  obtain ⟨hu, -, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig h _ V.gram hJ m X Y hW T (top T) (top_le T) (lt_top_iff T)
    (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) fun _ => rfl
  have hC := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (GlobalTheory.SiegelSet.sigma_sigma h) hJ (top_le T)
  have hc' : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.UAut.unipFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card)) φ c := hu ▸ hc
  have hΓ : ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ GlobalTheory.UAut.parFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) : Subgroup (GA D V)) : Set (GA D V)) ⊆
      (leftSub V X Y S : Set (GA D V)) := by
    intro p hp
    have e := leftGrp_eq h hJ hW S
    have : p ∈ GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) :=
      Subgroup.mem_sup_right ⟨hp.1, parFlag_le_of_subset X hST (top_le S) (top_le T) (top_mono hST) (lt_top_iff S) hp.2⟩
    rw [e] at this
    exact this
  obtain ⟨r1, r2⟩ := isSmModOn_constTermOn h hJ _ hC hΓ hφ hc'
  refine ⟨?_, fun l hl => ?_⟩
  · have e : (leftSub V X Y T : Subgroup (GA D V)) = GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
        (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) := (leftGrp_eq h hJ hW T).symm
    rw [e]
    exact r1
  · have := r2 l hl
    rw [← hu] at this
    exact this

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInheritedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_moderate_growth_inherited : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod.isSmModOn_constAlong <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

open MeasureTheory GlobalTheory.SiegelSet GlobalTheory.Mem.AutSpace GlobalTheory.SphSmooth

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def pairSpan (V : HSp D) (φ c : GA D V → ℂ) : Submodule ℂ ((GA D V → ℂ) × (GA D V → ℂ)) :=
  Submodule.span ℂ {p | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧
    p = (l.foldr lineDer φ, l.foldr lineDer c)}

theorem pairSpan_le (φ c : GA D V → ℂ) : pairSpan V φ c ≤ (derSpan V φ).prod (derSpan V c) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩

theorem Rder_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (Rder θ V τ X p.1, Rder θ V τ X p.2) ∈ pairSpan V φ c := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨oneP θ V τ X :: l, List.forall_mem_cons.2 ⟨isRealLine_oneP hθ V hX, hl⟩, rfl⟩
  | zero =>
    have := Rder_smul (θ := θ) 0 (0 : GA D V → ℂ) τ X
    rw [zero_smul, zero_smul] at this
    simp only [Prod.fst_zero, Prod.snd_zero, this]
    exact zero_mem (pairSpan V φ c)
  | add x y hx hy ihx ihy =>
    have h1 := pairSpan_le φ c hx
    have h2 := pairSpan_le φ c hy
    simp only [Prod.fst_add, Prod.snd_add]
    rw [Rder_add (derSpan_le hθ hφ h1.1) (derSpan_le hθ hφ h2.1) hX,
      Rder_add (derSpan_le hθ hc h1.2) (derSpan_le hθ hc h2.2) hX]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    simp only [Prod.smul_fst, Prod.smul_snd, Rder_smul]
    exact Submodule.smul_mem _ a ih

theorem RderC_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (RderC θ V τ Z p.1, RderC θ V τ Z p.2) ∈ pairSpan V φ c := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  exact add_mem (Rder_mem_pairSpan hθ hφ hc h1 hp)
    (Submodule.smul_mem _ Complex.I (Rder_mem_pairSpan hθ hφ hc h2 hp))

theorem word_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (L : List ((GA D V → ℂ) → GA D V → ℂ)) (hL : ∀ A ∈ L, ∃ Z, A = RderC θ V τ Z) :
    (L.foldr (fun f acc => f acc) φ, L.foldr (fun f acc => f acc) c) ∈ pairSpan V φ c := by
  induction L with
  | nil => exact Submodule.subset_span ⟨[], by simp, rfl⟩
  | cons A L ih =>
    obtain ⟨Z, rfl⟩ := hL A List.mem_cons_self
    exact RderC_mem_pairSpan hθ hφ hc τ Z (ih fun B hB => hL B (List.mem_cons_of_mem _ hB))

theorem gelf_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (k : ℕ) : (gelf θ V τ k φ, gelf θ V τ k c) ∈ pairSpan V φ c := by
  have e : (gelf θ V τ k φ, gelf θ V τ k c) = ∑ idx : Fin (k + 1) → Fin V.rank,
      ((List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) φ,
        (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) c) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; rfl
    · rw [Prod.snd_sum]; rfl
  rw [e]
  refine Submodule.sum_mem _ fun idx _ => word_mem_pairSpan hθ hφ hc τ _ fun A hA => ?_
  obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hA
  exact ⟨_, rfl⟩

variable {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

theorem good_of_mem_pairSpan (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) {φ c : GA D V → ℂ}
    (hφ : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ)
    (h : ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) →
      IsConstAlong D.sp.cm.sig V.gram X T (l.foldr lineDer φ) (l.foldr lineDer c))
    (μ : Measure (unip D.sp.cm.sig V.gram X T)) (𝓕 : Set (unip D.sp.cm.sig V.gram X T)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram).subgroupOf (unip D.sp.cm.sig V.gram X T)) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (g : GA D V) {p : (GA D V → ℂ) × (GA D V → ℂ)} (hp : p ∈ pairSpan V φ c) :
    IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => p.1 ((u : GA D V) * g)) 𝓕 μ ∧
      p.2 g = ∫ u in 𝓕, p.1 ((u : GA D V) * g) ∂μ := by
  have hJ : IsHermND D.sp.cm.sig V.gram :=
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨?_, h l hl μ 𝓕 hμ h𝓕 h1 g⟩
    obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ _ X Y hW T
    have hcont := GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ φ hφ.level hφ.cont hφ.smooth l hl
    have hleft := GlobalTheory.UAut.ConstAut.leftInv_foldr
      (Γ := (GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V))) (φ := φ) (fun γ hγ x => hφ.left γ hγ x) l
    refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _
      (hcont.comp (continuous_subtype_val.mul continuous_const)) fun γ hγ u => ?_
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hleft γ ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩ _
  | zero => exact ⟨integrableOn_zero, by simp⟩
  | add x y _ _ ihx ihy =>
    refine ⟨ihx.1.add ihy.1, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [ihx.2, ihy.2]
    exact (integral_add ihx.1 ihy.1).symm
  | smul a x _ ih =>
    refine ⟨ih.1.const_mul a, ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [ih.2]
    exact (integral_const_mul a _).symm

theorem isConstAlong_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  intro D θ hθ V m X Y hW T φ c hφ hc h τ k μ 𝓕 hμ h𝓕 h1 g
  have sφ : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram φ := hφ.smooth
  exact (good_of_mem_pairSpan hW T hφ h μ 𝓕 hμ h𝓕 h1 g
    (gelf_mem_pairSpan hθ (mem_smFun_of_isSm hθ sφ) (mem_smFun_of_isSm hθ hc) τ k)).2

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_smooth_moderate_growth : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf.isConstAlong_gelf <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FormsSubsetFormsOnEmpty
section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteDimensionalOfParts
section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FiniteSlicesUPart
section -- merged from Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.CoeffSpanCompMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem coeffSpan_comp_mem {K K' W : Type} [Group K] [Group K'] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) (j : K' →* K) {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (f ∘ j) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j) := by
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨ℓ, w, rfl⟩ := h
    exact Submodule.subset_span ⟨ℓ, w, rfl⟩
  | zero => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).zero_mem
  | add a b _ _ ha hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).add_mem ha hb
  | smul a b _ hb => exact (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp j)).smul_mem a hb

theorem finite_slices_core : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) 1)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hXY T _hT hAd
  obtain ⟨V', ι, hι, hran⟩ := GlobalTheory.T.exists_orthogonal_hermitian_subspace D V m X Y hXY T
  obtain ⟨s, hsc, hsrel, hsq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have hs : ∀ h, EmbRel V V' ι (s h) h := fun h => (hsrel h (s h)).2 rfl
  obtain ⟨hsu, hsurj, hsf⟩ := GlobalTheory.T.orthogonal_subspace_unitary_embedding D V m X Y hXY T V' ι hι hran s hs
  obtain ⟨ε', fr', j, hfr', hj, hk⟩ := GlobalTheory.T.frame_adapted_subspace_unitary_group D θ hθ V ε fr hfr m X Y hXY T hAd V' ι hι hran s hs
  obtain ⟨A, hA⟩ := GlobalTheory.T.constant_term_parabolic_eigenfunction D θ hθ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs
  let U' : Subgroup (GA D V') := U.comap s
  have hU' : IsOpen (U' : Set (GA D V')) := hU.preimage hsc
  let ρ' : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε' τ)) (W τ) := fun τ => (ρ τ).comp (j τ)
  have hρ' : ∀ τ, IsContRep (ρ' τ) := fun τ ℓ w => (hρ τ ℓ w).comp (hj τ)
  let B : Set (GA D V' → ℂ) := {φ | IsAutFunSm θ V' φ ∧ (∀ u ∈ U', u ∈ GfC V' → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V' τ (ε' τ) (fr' τ) (ρ' τ) φ) ∧ IsCuspFun V' φ ∧
    ∀ τ, (A τ 1).foldr (fun a f => gelf θ V' τ 1 f - a • f) φ = 0}
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ B) :=
    GlobalTheory.T.constant_term_parabolic_finite_type D θ hθ V' U' hU' ε' fr' hfr' W ρ' hρ' (fun τ => A τ 1)
  have hmem : ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T,
      (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → (fun h => ψ (s h * y)) ∈ B := by
    intro ψ hψ y hy hyc
    obtain ⟨h1, h2, h3, _⟩ := hψ.1
    have hcomm : ∀ h, s h * y = y * s h := fun h => hyc _ (hsu h)
    obtain ⟨hsm, hgr⟩ := GlobalTheory.T.constant_term_restrict_smooth_moderate D θ hθ V V' ι hι s hs _ ψ h1 y hcomm
    have hAF : IsAutFun V' (fun h => ψ (s h * y)) :=
      { left := fun γ hγ g => by
          have hm : s γ ∈ leftSub V X Y T :=
            Subgroup.mem_sup_right ⟨hsq γ hγ, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hsu γ)⟩
          simp only [map_mul]
          rw [mul_assoc]
          exact h1.left _ hm _
        level := ⟨U', hU', fun k hk hk' g => by
          simp only [map_mul]
          rw [mul_assoc, hcomm k, ← mul_assoc]
          exact h2 _ hk (hsf k hk') _⟩
        cont := h1.cont.comp (hsc.mul continuous_const) }
    refine ⟨GlobalTheory.T.smooth_automorphic_derivative_growth D θ hθ V' _ hAF hsm hgr (fun τ k => ⟨A τ k, hA ψ hψ.1 y hy hyc τ k⟩),
      ?_, fun τ x => ?_,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.isCuspFun_slice D θ V U ε fr W ρ c m X Y hXY T V' ι hι hran s hs ψ hψ y hy hyc, fun τ => hA ψ hψ.1 y hy hyc τ 1⟩
    · intro k hk hk' g
      simp only [map_mul]
      rw [mul_assoc, hcomm k, ← mul_assoc]
      exact h2 _ hk (hsf k hk') _
    · have e : (fun k => ψ (s (x * kAt θ V' τ (ε' τ) (fr' τ) k) * y)) =
          (fun k0 => ψ ((s x * y) * kAt θ V τ (ε τ) (fr τ) k0)) ∘ j τ := by
        funext k
        simp only [Function.comp, map_mul]
        rw [mul_assoc, hcomm, ← mul_assoc, ← hk τ k]
      rw [e]
      exact coeffSpan_comp_mem (ρ τ) (j τ) (h3 τ (s x * y))
  let s' : GA D V' → uPart D.sp.cm.sig V.gram X Y T := fun h => ⟨s h, hsu h⟩
  have hs' : Function.Surjective s' := fun g => by
    obtain ⟨h, hh⟩ := hsurj g.1 g.2
    exact ⟨h, Subtype.ext hh⟩
  let Φ := LinearMap.funLeft ℂ ℂ s'
  have hΦ : Function.Injective Φ := LinearMap.funLeft_injective_of_surjective _ _ _ hs'
  set P := Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T)
    (levi D.sp.cm.sig V.gram X Y T) 1)
  have hle : P.map Φ ≤ Submodule.span ℂ B := by
    rw [Submodule.map_span_le]
    rintro f ⟨ψ, hψ, y, hy, hyc, rfl⟩
    apply Submodule.subset_span
    have := hmem ψ hψ y hy hyc
    convert this using 1
    funext h
    simp [Φ, s', LinearMap.funLeft]
  haveI : FiniteDimensional ℂ (P.map Φ) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective Φ hΦ P).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem finite_slices_uPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hWF T hT b
  obtain ⟨n, hn, mm, hmm, b₀, hb, had⟩ := GlobalTheory.T.langlands_decomposition_unipotent_levi D θ hθ V ε fr hfr m X Y hWF T b
  obtain ⟨mH, hmH, mo, hmo, hcomm, rfl⟩ := GlobalTheory.T.levi_decomposition_hermitian_centralizer D V m X Y hWF T mm hmm
  subst hb
  have hU' : IsOpen ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) =
        (fun x => b₀⁻¹ * x * b₀) ⁻¹' (U : Set (GA D V)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [mul_assoc] using hu
      · intro hx
        exact ⟨b₀⁻¹ * x * b₀, hx, by group⟩
    rw [e]
    exact hU.preimage (by fun_prop)
  have hfr' := GlobalTheory.T.frame_family_right_translate D θ hθ V ε fr hfr b₀
  have hfin := finite_slices_core D θ hθ V _ hU' ε _ hfr' W ρ hρ c m X Y hWF T hT had
  set H := uPart D.sp.cm.sig V.gram X Y T with hH
  set L := levi D.sp.cm.sig V.gram X Y T with hL
  let mH' : H := ⟨mH, hmH⟩
  let R : (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun f t => f (t * mH')
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : sliceSet (cuspOn θ V X Y T U ε fr ρ c) H L (n * (mH * mo) * b₀) ⊆
      ((Submodule.span ℂ (sliceSet (cuspOn θ V X Y T (U.map (MulAut.conj b₀).toMonoidHom) ε
        (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) ρ c) H L 1)).map R : Set (H → ℂ)) := by
    rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
    refine ⟨fun t : H => φ ((t : GA D V) * (y * mo) * b₀),
      Submodule.subset_span ⟨fun x => φ (x * b₀), GlobalTheory.T.constant_term_frame_K_type_coefficients D θ hθ V U ε fr hfr W ρ c m X Y T φ hφ b₀, y * mo,
        mul_mem hy hmo, fun t ht => ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc, hyc t ht, mul_assoc, hcomm t ht, mul_assoc]
    · funext t
      simp [mul_assoc]
    · funext t
      have ht : (t : GA D V) ∈ L := GlobalTheory.T.hermitian_part_le_levi D V m X Y T t.2
      have hty : (t : GA D V) * y ∈ L := mul_mem ht hy
      have hγ : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ ∈ unip D.sp.cm.sig V.gram X T :=
        GlobalTheory.T.levi_normalizes_unipotent_variant D V m X Y hWF T _ hty n hn
      have hleft := hφ.1.1.left _ (Subgroup.mem_sup_left hγ : _ ∈ (leftSub V X Y T : Subgroup (GA D V)))
        ((t : GA D V) * y * (mH * mo * b₀))
      have e1 : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ * ((t : GA D V) * y * (mH * mo * b₀)) =
          (t : GA D V) * y * (n * (mH * mo) * b₀) := by group
      have e2 : (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * mH * (y * mo) * b₀ := by
        have := hyc mH hmH
        calc (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * (y * mH) * mo * b₀ := by group
          _ = (t : GA D V) * (mH * y) * mo * b₀ := by rw [this]
          _ = (t : GA D V) * mH * (y * mo) * b₀ := by group
      change φ ((t : GA D V) * mH * (y * mo) * b₀) = φ ((t : GA D V) * y * (n * (mH * mo) * b₀))
      rw [← e1, hleft, e2]
  haveI := hfin
  exact Submodule.finiteDimensional_of_le (Submodule.span_le.2 hsub)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem finiteDimensional_of_parts {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (L : Subgroup G) (hgen : L = ⨆ i, H i)
    (𝓒 : Set (G → ℂ)) (B : Finset G)
    (hB : ∀ φ ∈ Submodule.span ℂ 𝓒, (∀ b ∈ B, ∀ g ∈ L, φ (g * b) = 0) → φ = 0)
    (hcore : ∀ i b, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet 𝓒 (H i) L b))) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓒) := by
  let P : (∀ i, H i) →* G := Subgroup.noncommPiCoprod hcomm
  have hrange : P.range = L := by rw [Subgroup.noncommPiCoprod_range, hgen]
  have hP : ∀ i (t : H i), P (Pi.mulSingle i t) = t := fun i t => Subgroup.noncommPiCoprod_mulSingle i t

  let R : G → (G → ℂ) →ₗ[ℂ] ((∀ i, H i) → ℂ) := fun b => LinearMap.funLeft ℂ ℂ fun x => P x * b
  have hfin : ∀ b, FiniteDimensional ℂ (Submodule.span ℂ (R b '' 𝓒)) := fun b => by
    haveI := fun i => hcore i b
    refine finiteDimensional_of_slices (fun i => Submodule.span ℂ (sliceSet 𝓒 (H i) L b)) _ ?_
    rintro _ ⟨φ, hφ, rfl⟩ i x
    have e : ∀ t : H i, Function.update x i t = Pi.mulSingle i t * Function.update x i 1 := fun t => by
      simpa only [Pi.mulSingle, one_mul, mul_one] using
        (Function.update_mul (1 : ∀ j, H j) x i t 1)
    have e' : ∀ t : H i, Function.update x i t = Function.update x i 1 * Pi.mulSingle i t := fun t => by
      simpa only [Pi.mulSingle, one_mul, mul_one] using
        (Function.update_mul x (1 : ∀ j, H j) i 1 t)
    refine Submodule.subset_span ⟨φ, hφ, P (Function.update x i 1), hrange ▸ ⟨_, rfl⟩, fun t ht => ?_, ?_⟩
    · have h1 := congrArg P ((e ⟨t, ht⟩).symm.trans (e' ⟨t, ht⟩))
      rwa [map_mul, map_mul, hP] at h1
    · funext t
      change φ (P (Function.update x i t) * b) = φ ((t : G) * P (Function.update x i 1) * b)
      rw [e t, map_mul, hP]
  have hmap : ∀ b, ∀ φ ∈ Submodule.span ℂ 𝓒, R b φ ∈ Submodule.span ℂ (R b '' 𝓒) := fun b φ hφ => by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hφ
  let Ψ : Submodule.span ℂ 𝓒 →ₗ[ℂ] (∀ b : B, Submodule.span ℂ (R b.1 '' 𝓒)) :=
    LinearMap.pi fun b => ((R b.1).comp (Submodule.span ℂ 𝓒).subtype).codRestrict _ fun φ => hmap b.1 φ.1 φ.2
  haveI := fun b : B => hfin b.1
  refine FiniteDimensional.of_injective Ψ ((injective_iff_map_eq_zero Ψ).2 fun φ hφ => ?_)
  refine Subtype.ext (hB φ.1 φ.2 fun b hb g hg => ?_)
  obtain ⟨x, rfl⟩ : g ∈ P.range := hrange ▸ hg
  exact congrFun (congrArg Subtype.val (congrFun hφ ⟨b, hb⟩)) x

theorem finite_cuspOn : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT
  classical
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨B, hB⟩ := GlobalTheory.T.archimedean_frame_K_type_decomposition D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  refine finiteDimensional_of_parts (part D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_parts_commute D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (levi D.sp.cm.sig V.gram X Y T)
    (GlobalTheory.T.levi_eq_iSup_parts D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T) (cuspOn θ V X Y T U ε fr ρ c) B
    (fun φ hφ h => hB φ (mem_formsOn_of_mem_span hθ (Submodule.span_mono (show cuspOn θ V X Y T U ε fr ρ c ⊆ formsOn θ V X Y T U ε fr ρ c from fun _ hf => hf.1) hφ)) h) ?_
  rintro (_ | k) b
  · exact UCore.Rg.finite_slices_uPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT b
  · exact CoreGL.Rg.finite_slices_glPart D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT k.1 k.2 b

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

section Main

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem host_facts (D : D7) (V : HSp D) : IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ IsHermND D.sp.cm.sig V.gram :=
  let h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  ⟨h.1, h.2 V⟩

theorem forms_subset_formsOn_empty (hθ : IsInfFam θ) :
    forms θ V U ε fr ρ c ⊆ formsOn θ V X Y ∅ U ε fr ρ c := by
  rintro φ ⟨h1, h2, h3, h4⟩
  have hle : (leftSub V X Y ∅ : Set (GA D V)) ⊆ GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram := by
    have : leftSub V X Y ∅ ≤ GQ V := by
      refine sup_le ?_ inf_le_left
      rw [unip_empty]
      exact bot_le
    exact this
  exact ⟨IsSmModOn.of_isSmoothModerate (GlobalTheory.SiegelSet.isSmoothModerate_of_isAutFunSm hθ h1) hle, h2, h3, h4⟩

theorem constAlong_mem_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) {S T : Finset (Fin m)} (hST : S ⊆ T) (hT : T.Nonempty)
    {φ a : GA D V → ℂ} (hφ : φ ∈ formsOn θ V X Y S U ε fr ρ c) (ha : IsConstAlong D.sp.cm.sig V.gram X T φ a) :
    a ∈ formsOn θ V X Y T U ε fr ρ c := by
  obtain ⟨h1, h2, h3, h4⟩ := hφ
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  obtain ⟨m1, m2⟩ := GlobalTheory.T.constant_term_moderate_growth_inherited D V m X Y hW S T hST hT φ a h1 ha
  obtain ⟨-, μ, 𝓕, b1, b2, b3⟩ := st.1 T
  have hleft : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ :=
    ⟨fun γ hγ g => h1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW S T hST hγ) g, h1.level, h1.cont, h1.smooth, h1.growth⟩
  refine ⟨m1, fun u hu hu' g => ?_, fun τ => GlobalTheory.T.constant_term_parabolic_K_finite D θ V m X Y hW S T hST τ (ε τ) (fr τ) (W τ) (ρ τ) φ a h1 (h3 τ) ha,
    fun τ k => ?_⟩
  · rw [ha μ 𝓕 b1 b2 b3 (g * u), ha μ 𝓕 b1 b2 b3 g]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x => ?_)
    change φ (_ * (g * u)) = φ (_ * g)
    rw [← mul_assoc, h2 u hu hu']
  · have g1 := GlobalTheory.T.constant_term_smooth_moderate_growth D θ hθ V m X Y hW T φ a hleft m1.smooth m2 τ k
    rw [h4 τ k] at g1
    have g2 : IsConstAlong D.sp.cm.sig V.gram X T (c τ k • φ) (c τ k • a) := fun μ 𝓕 b1 b2 b3 g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [ha μ 𝓕 b1 b2 b3 g, MeasureTheory.integral_const_mul]
    exact st.2.2.1 T _ _ _ g1 g2

theorem finite_formsOn [∀ τ, FiniteDimensional ℂ (W τ)] (hθ : IsInfFam θ) (hU : IsOpen (U : Set (GA D V)))
    (hfr : IsFrameFam V ε fr) (hρ : ∀ τ, IsContRep (ρ τ)) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) :
    ∀ (j : ℕ) (T : Finset (Fin m)), T.Nonempty → Tᶜ.card = j →
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c)) := by
  classical
  obtain ⟨hcm, hJ⟩ := host_facts D V
  have st := constAlong_cocompact_unique_stages hcm hJ hW
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro T hT hj
  set A := Submodule.span ℂ (formsOn θ V X Y T U ε fr ρ c) with hA
  have hmem : ∀ f : A, f.1 ∈ formsOn θ V X Y T U ε fr ρ c := fun f => mem_formsOn_of_mem_span hθ f.2
  have hl : ∀ f : A, ∀ T' : Finset (Fin m), T ⊆ T' → GlobalTheory.AutomorphicL2Unitary.LeftInv
      (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X T') f.1 := fun f T' h γ hγ g =>
    (hmem f).1.left γ (GlobalTheory.T.rational_unipotent_le_parabolic D V m X Y hW T T' h hγ) g

  have key : ∀ k : {k // k ∉ T}, ∃ L : A →ₗ[ℂ] Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c),
      ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1 (L f).1 := by
    intro k
    have hsub : T ⊆ insert k.1 T := Finset.subset_insert _ _
    haveI := locallyCompact_unip hcm hJ hW (insert k.1 T)
    have cS := cocompact_unip_std hcm hJ hW (insert k.1 T)
    have cS' := cocompact_ratPts_inf le_rfl cS
    have hc : ∀ f : A, IsConstAlong D.sp.cm.sig V.gram X (insert k.1 T) f.1
        (GlobalTheory.Cusp.constTermOn (GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ unip D.sp.cm.sig V.gram X (insert k.1 T))
          (unip D.sp.cm.sig V.gram X (insert k.1 T)) f.1) := fun f =>
      (isConstTermOn_iff_ratPts_inf le_rfl cS (hl f _ hsub)).2 rfl
    refine ⟨{ toFun := fun f => ⟨_, Submodule.subset_span
                (constAlong_mem_formsOn hθ hW hsub (Finset.insert_nonempty _ _) (hmem f) (hc f))⟩
              map_add' := fun a b => Subtype.ext (funext fun x =>
                cS'.constTermOn_add (hl a _ hsub) (hmem a).1.cont (hl b _ hsub) (hmem b).1.cont x)
              map_smul' := fun a f => Subtype.ext (funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x) }, hc⟩
  choose L hL using key
  have hfin : ∀ k : {k // k ∉ T},
      FiniteDimensional ℂ (Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := fun k => by
    have hlt : (insert k.1 T)ᶜ.card < j := by
      rw [← hj]
      refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hx ⊢
        exact hx.2
      · have := h (Finset.mem_compl.2 k.2)
        simp at this
    exact ih _ hlt _ (Finset.insert_nonempty _ _) rfl
  let Ψ : A →ₗ[ℂ] (∀ k : {k // k ∉ T}, Submodule.span ℂ (formsOn θ V X Y (insert k.1 T) U ε fr ρ c)) := LinearMap.pi L
  have hker : ∀ f : A, Ψ f = 0 → ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' f.1 0 := by
    intro f hf T' hT'
    obtain ⟨k, hk, hkT⟩ := Finset.exists_of_ssubset hT'
    have h0 : (L ⟨k, hkT⟩ f).1 = 0 := congrArg Subtype.val (congrFun hf ⟨k, hkT⟩)
    have h1 := hL ⟨k, hkT⟩ f
    rw [h0] at h1
    exact st.2.2.2.2 T' (insert k T) f.1 0 0 (Finset.insert_subset hk hT'.1) (hmem f).1.cont
      (fun γ hγ hγ' g => hl f T' hT'.1 γ ⟨hγ, hγ'⟩ g) h1 (isConstAlong_const _ _ _ _ 0)
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Rg.finite_cuspOn D θ hθ V U hU ε fr hfr W ρ hρ c m X Y hW T hT
  haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by
    let ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧
        ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0} :=
      { toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective ι fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
  haveI := hfin
  haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)

end Main

theorem finite_constTerm : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.Published.AutFin.IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ c : D.what₂.Tau → ℕ → ℂ, ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C), FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) '' GlobalTheory.Published.AutFin.forms θ V U ε fr ρ c)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c r C hC
  obtain ⟨hcm, hJ⟩ := host_facts D V
  obtain ⟨hr, hi, hg⟩ := id hC
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, hm, X, Y, hW, hX⟩ := GlobalTheory.WittExt.exists_isWittFrame_initCols D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ r C hi hg
  have hfin := finite_formsOn (c := c) (U := U) hθ hU hfr hρ hW _ {(⟨r, hm⟩ : Fin m)} (Finset.singleton_nonempty _) rfl
  haveI := hfin
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (formsOn θ V X Y {(⟨r, hm⟩ : Fin m)} U ε fr ρ c))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, hφ, rfl⟩
  refine Submodule.subset_span ?_
  have h0 := forms_subset_formsOn_empty (X := X) (Y := Y) hθ hφ
  refine constAlong_mem_formsOn hθ hW (Finset.empty_subset _) (Finset.singleton_nonempty _) h0 ?_
  rw [isConstAlong_singleton hW, hX, GlobalTheory.UAut.isConstTerm_iff]
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram C := GlobalTheory.Cusp.NA_frameFlag hC
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC)) φ
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) φ) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hφ.1.left g, MeasureTheory.Measure.real, b3]
    simp
  exact e ▸ h1

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin.Rg
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCF.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin

section Sub

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {U : Subgroup (GA D V)} {ε : D.what₂.Tau → Fin V.rank → Bool}
  {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {W : D.what₂.Tau → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)}
  {c : D.what₂.Tau → ℕ → ℂ}

theorem forms_add {f g : GA D V → ℂ} (hf : f ∈ forms θ V U ε fr ρ c) (hg : g ∈ forms θ V U ε fr ρ c) :
    f + g ∈ forms θ V U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨GlobalTheory.MultMem.isAutFunSm_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
  · exact (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f f1.smooth g g1.smooth, f4, g4, smul_add]

theorem forms_smul (a : ℂ) {f : GA D V → ℂ} (hf : f ∈ forms θ V U ε fr ρ c) :
    a • f ∈ forms θ V U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨GlobalTheory.MultMem.isAutFunSm_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.smul_apply, f2 u hu hu' x]
  · exact (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).smul_mem a (f3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]

theorem forms_zero : (0 : GA D V → ℂ) ∈ forms θ V U ε fr ρ c := by
  refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, fun _ _ _ _ => rfl, fun τ x => (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
  have := (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
  simpa using this

theorem mem_forms_of_mem_span {f : GA D V → ℂ} (hf : f ∈ Submodule.span ℂ (forms θ V U ε fr ρ c)) :
    f ∈ forms θ V U ε fr ρ c := by
  induction hf using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact forms_zero
  | add x y _ _ hx hy => exact forms_add hx hy
  | smul a x _ hx => exact forms_smul a hx

end Sub

theorem finite_of_cusp_of_constTerm {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type)
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ))
    (c : D.what₂.Tau → ℕ → ℂ)
    (hcusp : FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ}))
    (hct : ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C),
      FiniteDimensional ℂ (Submodule.span ℂ
        (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) '' forms θ V U ε fr ρ c))) :
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V U ε fr ρ c)) := by
  classical
  set S := Submodule.span ℂ (forms θ V U ε fr ρ c) with hS
  have hmem : ∀ f : S, f.1 ∈ forms θ V U ε fr ρ c := fun f => mem_forms_of_mem_span f.2

  let hex : ℕ → Prop := fun r => ∃ C : Matrix (Fin V.rank) (Fin r) D.host.E, IsIsoFrame V C
  let Tm : ∀ r, hex r → (S →ₗ[ℂ] (GA D V → ℂ)) := fun r h =>
    { toFun := fun f => GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) f.1
      map_add' := fun a b => funext fun x =>
        (GlobalTheory.Cusp.cocompact_single _).constTermOn_add (hmem a).1.left (hmem a).1.cont (hmem b).1.left (hmem b).1.cont x
      map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }
  let R : Fin (V.rank + 1) → Submodule ℂ (GA D V → ℂ) := fun i =>
    if h : hex i.val then Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c) else ⊥
  have hRfin : ∀ i, FiniteDimensional ℂ (R i) := fun i => by
    by_cases h : hex i.val
    · have e : R i = Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c) :=
        dif_pos h
      rw [e]; exact hct _ _ h.choose_spec
    · have e : R i = ⊥ := dif_neg h
      rw [e]; infer_instance
  let T : ∀ i : Fin (V.rank + 1), S →ₗ[ℂ] R i := fun i =>
    if h : hex i.val then
      (Tm i.val h).codRestrict (R i) (fun f => by
        simp only [R, dif_pos h]
        exact Submodule.subset_span ⟨f.1, hmem f, rfl⟩)
    else 0
  let Ψ : S →ₗ[ℂ] (∀ i, R i) := LinearMap.pi T
  have hker : ∀ f : S, Ψ f = 0 → IsCuspFun V f.1 := by
    intro f hf
    have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f.1 := (hmem f).1.left
    refine (GlobalTheory.Cusp.isCuspFun_iff hl).2 fun Y hY => ?_
    obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V Y).1 hY
    have hr : r ≤ V.rank := by
      have := hC.2.1.fintype_card_le_finrank
      simpa using this
    have hx : hex r := ⟨C, hC⟩
    have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hx.choose_spec) f.1 = 0 := by
      have := congrFun hf ⟨r, Nat.lt_succ_of_le hr⟩
      have h2 := congrArg Subtype.val this
      simpa [Ψ, T, hx, Tm] using h2
    exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V r _ C hx.choose_spec hC f.1 hl h0
  haveI := hcusp
  haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by
    let ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ} :=
      { toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective ι fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
  haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance
  haveI : FiniteDimensional ℂ (S ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCF.Rg

namespace GlobalTheory.CompanionTheory.Hypotheses₂


open GlobalTheory.Published.AutFin in
theorem _root_.PositivityTheory.RgHf.harishChandraFinite : GlobalTheory.Published.HarishChandraFinite := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c
  exact HCF.Rg.finite_of_cusp_of_constTerm θ V U ε fr W ρ c (GlobalTheory.CompanionTheory.HCCusp.cuspFinite D θ hθ V U hU ε fr hfr W ρ hρ c)
    (ConstFin.Rg.finite_constTerm D θ hθ V U hU ε fr hfr W ρ hρ c)

end GlobalTheory.CompanionTheory.Hypotheses₂

end

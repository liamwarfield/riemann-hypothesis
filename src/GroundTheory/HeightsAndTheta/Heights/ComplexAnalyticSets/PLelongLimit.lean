module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalLimitGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology Set Function
open scoped ContDiff Manifold

theorem tendsto_of_forall_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι} (T : ι → (E → ℝ) → ℝ) (L : (E → ℝ) → ℝ)
    (hT : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → ∀ᶠ ε in l, T ε (f + g) = T ε f + T ε g)
    (hL : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → L (f + g) = L f + L g)
    (hloc : ∀ p : E, ∃ N ∈ 𝓝 p, ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ N → Tendsto (fun ε => T ε f) l (𝓝 (L f)))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε => T ε f) l (𝓝 (L f)) := by
  choose N hN hNf using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_tsupport f)
    (fun p => interior (N p)) (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hN x)⟩)
  obtain ⟨g, hg⟩ : ∃ g : E → E → ℝ, g = fun i x => ρ i x * f x := ⟨_, rfl⟩
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => by
    rw [hg]; exact (ρ i).contMDiff.contDiff.mul hf
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => by
    rw [hg]; exact hfc.mul_left
  have hgN : ∀ i, tsupport (g i) ⊆ N i := fun i => by
    rw [hg]; exact tsupport_mul_subset_left.trans ((hρ i).trans interior_subset)
  have hfin : {i | (support (ρ i) ∩ tsupport f).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hfc
  have hsum : f = ∑ i ∈ hfin.toFinset, g i := by
    funext x
    simp only [Finset.sum_apply, hg]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · rw [← finsum_eq_sum_of_support_subset (fun i => ρ i x), ρ.sum_eq_one hx, one_mul]
      intro i hi
      simp only [Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨x, hi, hx⟩
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hT0 : ∀ᶠ ε in l, T ε 0 = 0 := by
    filter_upwards [hT 0 0 contDiff_const HasCompactSupport.zero contDiff_const
      HasCompactSupport.zero] with ε h
    simpa using h
  have hL0 : L 0 = 0 := by
    simpa using hL 0 0 contDiff_const HasCompactSupport.zero contDiff_const HasCompactSupport.zero
  have key : ∀ s : Finset E, ContDiff ℝ ∞ (∑ i ∈ s, g i) ∧ HasCompactSupport (∑ i ∈ s, g i) ∧
      (∀ᶠ ε in l, T ε (∑ i ∈ s, g i) = ∑ i ∈ s, T ε (g i)) ∧
      L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨contDiff_const, HasCompactSupport.zero, hT0, hL0⟩
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [Finset.sum_insert ha]
      refine ⟨(hgs a).add h1, (hgc a).add h2, ?_, ?_⟩
      · filter_upwards [hT (g a) _ (hgs a) (hgc a) h1 h2, h3] with ε e1 e2
        rw [e1, e2]
      · rw [hL (g a) _ (hgs a) (hgc a) h1 h2, h4]
  obtain ⟨-, -, hTs, hLs⟩ := key hfin.toFinset
  rw [hsum, hLs]
  exact (tendsto_finsetSum _ fun i _ => hNf i (g i) (hgs i) (hgc i) (hgN i)).congr'
    (hTs.mono fun ε h => h.symm)

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem varInt_eq_zero_of_vanish {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by
  classical
  unfold varInt
  split_ifs with h
  · have h0 : chartDens W h.choose f φ = fun _ => 0 := by
      funext y
      unfold chartDens sheetSum
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      rw [finsum_eq_dif]
      by_cases hx : x ∈ ComplexSets.fibre W h.choose y
      · rw [dite_eq_left hx]
        split_ifs
        · show f x * _ = 0
          rw [hf x hx.1, zero_mul]
        · rfl
      · rw [dite_eq_right hx]
    simp [chartInt, h0]
  · rfl

theorem LelongLimit.proof (hOff : LelongLimitOffZero.Statement) (hOn : LelongLimitOnZero.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimit.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hW : ∀ W ∈ S, W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
    intro W hWm
    have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
    refine ⟨hWm.1.1,
      fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
    have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
    simpa [linForm, linEval] using this
  have hφW : ∀ W ∈ S, ∀ i, SmoothNear (zeroSet W) (φ i) := fun W hWm i => by
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, (hW W hWm).2.1.trans hSU, hC⟩
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) ?_ ?_ ?_ f hf hfc
  · intro g₁ g₂ h1 h1c h2 h2c
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · intro g₁ g₂ h1 h1c h2 h2c
    rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    rw [hAdd n d W g₁ g₂ φ (hW W hWm).1 h1.continuous h1c h2.continuous h2c (hφW W hWm), mul_add]
  · intro p
    by_cases hp : p ∈ zeroSet J ∩ {x | linEval u x = 0}
    · exact hOn n d J u φ p hJ hdim hu hφ hp.1 hp.2
    · refine ⟨_, hclosed.isOpen_compl.mem_nhds hp, fun g hg hgc hgN => ?_⟩
      have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
        rw [finsum_eq_dif]
        by_cases hWm : W ∈ S
        · rw [dite_eq_left hWm, varInt_eq_zero_of_vanish W g φ fun x hx =>
            image_eq_zero_of_notMem_tsupport fun hxs =>
              hgN hxs ⟨(hW W hWm).2.1 hx, (hW W hWm).2.2 x hx⟩, mul_zero]
        · rw [dite_eq_right hWm]
      simp only [h0]
      exact hOff n d J u g φ hJ hdim hu hg hgc hφ (Set.disjoint_left.2 fun x hx hx' => hgN hx hx')

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

theorem exists_eval_ne_zero_of_isOpen_pi {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hF
  have hinf : ∀ i, (u i).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)
  refine (funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hsub hy)

theorem SliceReducedAway.proof (hZ : SliceReducedAwayZariski.Statement) :
    SliceReducedAway.Statement := by
  intro n d J q hJ
  obtain ⟨F, hF, hgood⟩ := hZ n d J q hJ
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hφ : Continuous φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ :=
      exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩
    exact ⟨φ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensChain

variable {D : ℕ}

theorem fderiv_comp_real (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (h ∘ g) y = deriv h (g y) • fderiv ℝ g y :=
  (hh.hasDerivAt.comp_hasFDerivAt y hg.hasFDerivAt).fderiv

theorem dz_cplx_comp (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by
  rw [dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dzb_cplx_comp (k : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dzb k (cplx g) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem hessC_comp_real (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by
  obtain ⟨U, hU, hzU, hgU, -⟩ := MaDensLeibniz.exists_open_contDiffOn g g z hg hg
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' (n := 1)).differentiable (by norm_num)
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_comp k F g y (hF1 _)
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z := by
    have h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y) := by
      funext y; simp [cplx]
    rw [h]
    exact Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)
  have hB := differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)
  rw [dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]
  simp only [gradMat, cplx, Function.comp_apply]
  ring

theorem gradMat_comp (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    gradMat (F ∘ g) (F ∘ g) z = ((deriv F (g z) ^ 2 : ℝ) : ℂ) • gradMat g g z := by
  ext j k
  simp only [gradMat, Matrix.smul_apply, smul_eq_mul]
  rw [dz_cplx_comp j F g z hF hg, dzb_cplx_comp k F g z hF hg]
  push_cast
  ring

theorem proof : MaDensChain.Statement := by
  intro D φ F g z hF hg
  have hF1 : DifferentiableAt ℝ F (g z) := (hF.differentiable (by norm_num)) _
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]
    unfold gradDens
    rw [mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · unfold gradDens
    rw [gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring

end MaDensChain

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace TubeDeepRankOne

theorem mdisc_vecMulVec {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by
  rw [mdisc_eq_sum_perm]
  congr 1
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det =
        (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j)) := by
    intro σ
    have h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) =
        Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j := by
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [h1, det_mul_row, det_permute', det_transpose]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) =
      starRingEnd ℂ (Matrix.of u).det := by
    rw [RingHom.map_det, det_apply']
    rfl
  rw [hconj, Complex.mul_conj]

theorem mdisc_cons_sum {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  obtain ⟨L, hL⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin (d + 1) => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  rw [← hL]
  have h := (L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)
  simpa [MultilinearMap.curryLeft_apply] using h

theorem hessC_euclPot_eq_one {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by
  have h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
    funext w
    simp [euclPot, Complex.normSq_eq_norm_sq]
  rw [h]
  exact hessC_sum_normSq z

theorem hessC_euclPot_comp {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    hessC (euclPot ∘ s) y = ∑ m, vecMulVec (fun j => jacC s y m j) (star fun j => jacC s y m j) := by
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [hessC_comp _ s y hs hE2, hessC_euclPot_eq_one, Matrix.mul_one]
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

theorem analyticAt_eval_poly {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem dz_logAbsSq {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by
  have hg := analyticAt_eval_poly P y
  have hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y :=
    hg.differentiableAt.hasFDerivAt
  have h1 := (hgd.restrictScalars ℝ).norm_sq
  have hne : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  have h2 := h1.log hne
  have hf : fderiv ℝ (logAbsSq P) y = _ := h2.fderiv
  set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc
  set p := eval y P with hp
  set w := c * (starRingEnd ℂ) p with hw
  have hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c := by
    rw [map_smul, smul_eq_mul]
  have hN : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hP).ne'
  have e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [← hc, hw]
    ring
  have e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p) := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [hI, hw]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hcp : c / p = w / (Complex.normSq p : ℂ) := by
    rw [← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]
  rw [dz_cplx, e1, e2, hcp]
  conv_rhs => rw [← Complex.re_add_im w]
  have hN' : (Complex.normSq p : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

theorem hessC_logAbsSq_sq_half {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0) :
    hessC (fun z => logAbsSq P z ^ 2 / 2) y =
      vecMulVec (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (star fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) := by
  have hg := analyticAt_eval_poly P y
  have hv : ContDiffAt ℝ 2 (logAbsSq P) y := by
    have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y :=
      ((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
    exact h1.log (by positivity)
  have hv0 : hessC (logAbsSq P) y = 0 := by
    have h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      norm_num
    rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_log_norm _ y hg hP, smul_zero]
  rw [MaDensLeibniz.hessC_sq_half _ y hv, hv0, smul_zero, zero_add, gradMat_eq_vecMulVec]
  have ha : (fun j => dz j (cplx (logAbsSq P)) y) =
      fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P :=
    funext fun j => dz_logAbsSq P y hP j
  rw [ha]

theorem fderiv_apply_coord {D m : ℕ} (F : (Fin D → ℂ) → Fin m → ℂ) (y h : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F y) (a : Fin m) :
    fderiv ℂ F y h a = fderiv ℂ (fun x => F x a) y h := by
  have e := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).hasFDerivAt.comp y
    hF.hasFDerivAt).fderiv
  have e' : (fun x => F x a) = (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a) ∘ F := rfl
  rw [e', e]
  rfl

theorem det_rows_eq_deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : DifferentiableAt ℂ s y)
    (I : Fin d → Fin n) :
    (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
      (eval y P)⁻¹ * deepJacDet P s I y := by
  have hg := (analyticAt_eval_poly P y).differentiableAt
  have hF : DifferentiableAt ℂ (deepMap P s I) y := by
    refine differentiableAt_pi.2 fun k => ?_
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa [deepMap] using hg
    · simpa [deepMap] using differentiableAt_pi.1 hs (I i)
  set J := jacC (deepMap P s I) y with hJdef
  have hJ : (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)) =
      J.updateRow 0 ((eval y P)⁻¹ • J 0) := by
    ext k j
    refine Fin.cases ?_ (fun i => ?_) k
    · have h0 : (fun x => deepMap P s I x 0) = fun z => eval z P := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_zero, updateRow_self, Pi.smul_apply, smul_eq_mul, hJdef,
        jacC, fderiv_apply_coord _ _ _ hF, h0]
      rw [div_eq_inv_mul]
    · have hi : (fun x => deepMap P s I x i.succ) = fun x => s x (I i) := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_succ, updateRow_ne (Fin.succ_ne_zero i), hJdef, jacC,
        fderiv_apply_coord _ _ _ hF, hi, fderiv_apply_coord _ _ _ hs]
  rw [hJ, det_updateRow_smul, updateRow_eq_self, hJdef, det_jacC]
  rfl

theorem proof : TubeDeepRankOne.Statement := by
  intro n d A P U s y hU hy hsd hAs hP
  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy
  set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha
  set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb
  have h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a) := by
    have hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2 := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simp only [Function.comp_apply, hAs z hz]
    rw [hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]
  have h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m)) := hessC_euclPot_comp s y hsa
  have hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) =
      (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa using h1
  have hI : ∀ I : Fin d → Fin n,
      (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)
        (star ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)) := by
    intro I
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hdet : ∀ I : Fin d → Fin n,
      (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
        (eval y P)⁻¹ * deepJacDet P s I y := fun I =>
    det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH, mdisc_cons_sum]
  simp_rw [hI, mdisc_vecMulVec, hdet]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d + 1).factorial_ne_zero
  have hre : ((1 / ((d + 1).factorial : ℂ)) *
      (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re =
      Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ) := by
    rw [show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hp : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  field_simp

end TubeDeepRankOne

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassPolynomialDivision
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MonicDifferenceQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

def monicDifferenceCoeff {d : ℕ} (C : Fin d → ℂ) (s : ℂ) (j : Fin d) : ℂ :=
  s ^ (d - 1 - (j : ℕ)) + ∑ k ∈ univ.filter (fun k : Fin d => (j : ℕ) < k), C k * s ^ ((k : ℕ) - 1 - j)

theorem sum_fin_ite_lt {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℂ) :
    ∑ j : Fin n, (if (j : ℕ) < m then f j else 0) = ∑ j ∈ range m, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then f j else 0) n, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

theorem sub_pow_eq_mul_sum_fin {n m : ℕ} (hm : m ≤ n) (s t : ℂ) :
    (s - t) * ∑ j : Fin n, (if (j : ℕ) < m then s ^ (m - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) = s ^ m - t ^ m := by
  rw [sum_fin_ite_lt hm (fun j => s ^ (m - 1 - j) * t ^ j), mul_comm]
  have h := geom_sum₂_mul s t m
  rw [geom_sum₂_comm] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem monic_sub_eq_mul_sum {d : ℕ} (C : Fin d → ℂ) (s t : ℂ) :
    (s ^ d + ∑ k : Fin d, C k * s ^ (k : ℕ)) - (t ^ d + ∑ k : Fin d, C k * t ^ (k : ℕ)) =
      (s - t) * ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) := by
  have expand : ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) =
      ∑ j : Fin d, (if (j : ℕ) < d then s ^ (d - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) +
        ∑ k : Fin d, C k * ∑ j : Fin d,
          (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) := by
    simp only [monicDifferenceCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
  have h2 : ∑ k : Fin d, (s - t) * (C k * ∑ j : Fin d,
      (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)) =
      ∑ k : Fin d, (C k * s ^ (k : ℕ) - C k * t ^ (k : ℕ)) :=
    Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, sub_pow_eq_mul_sum_fin k.isLt.le, mul_sub]
  rw [expand, mul_add, sub_pow_eq_mul_sum_fin le_rfl, Finset.mul_sum, h2, Finset.sum_sub_distrib]
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

namespace WeierstrassPolynomialDivision

theorem circleIntegral_finset_sum {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR)
      ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR),
      ih fun i hi => hf i (by simp [hi])]

theorem pointWithLast_eta {σ : Type} (x : Option σ → ℂ) : pointWithLast (fun i => x (some i)) (x none) = x := by
  funext o
  cases o <;> rfl

theorem differentiable_pointWithLast {σ : Type} [Fintype σ] :
    Differentiable ℂ (fun p : (σ → ℂ) × ℂ => pointWithLast p.1 p.2) := by
  rw [differentiable_pi]
  intro o
  cases o with
  | none => exact differentiable_snd
  | some i =>
    show Differentiable ℂ fun p : (σ → ℂ) × ℂ => p.1 i
    fun_prop

theorem norm_pointWithLast_lt {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro o
  cases o with
  | none => exact hs
  | some i => exact (norm_le_pi_norm z i).trans_lt hz

end WeierstrassPolynomialDivision


open WeierstrassPolynomialDivision in
theorem WeierstrassPolynomialDivision.proof (hC : ParametricCircleIntegralAnalytic.Statement) :
    WeierstrassPolynomialDivision.Statement := by
  intro σ _ d c g hc hc0 hg
  obtain ⟨εg, hεg, hgan⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨εc, hεc, hcan⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.eventually_all.2 fun j => (hc j).eventually_analyticAt)
  set ε := min εg εc with hε_def
  have hε : 0 < ε := lt_min hεg hεc
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε

  let G : (σ → ℂ) × ℂ → ℂ := fun p => g (pointWithLast p.1 p.2)
  let F : (σ → ℂ) × ℂ → ℂ := fun p => weierstrassPolynomial c (pointWithLast p.1 p.2)
  let A : Set ((σ → ℂ) × ℂ) := ball 0 ε ×ˢ ball 0 ε
  have hcd : ∀ z ∈ ball (0 : σ → ℂ) ε, ∀ j, DifferentiableAt ℂ (c j) z := fun z hz j =>
    (hcan z (mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _))) j).differentiableAt
  have hGd : ∀ p ∈ A, DifferentiableAt ℂ G p := by
    intro p hp
    have hp' : pointWithLast p.1 p.2 ∈ ball (0 : Option σ → ℂ) εg := mem_ball_zero_iff.2
      (norm_pointWithLast_lt hεg ((mem_ball_zero_iff.1 hp.1).trans_le (min_le_left _ _))
        ((mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)))
    exact (hgan _ hp').differentiableAt.comp p (differentiable_pointWithLast p)
  have hFd : ∀ p ∈ A, DifferentiableAt ℂ F p := by
    intro p hp
    show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, c j p.1 * p.2 ^ (j : ℕ)) p
    exact (differentiableAt_snd.pow d).add (DifferentiableAt.fun_sum fun j _ =>
      ((hcd p.1 hp.1 j).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))

  have hFne : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun s hs => ?_
    have hsn : ‖s‖ = r := mem_sphere_zero_iff_norm.1 hs
    have hA : ((0 : σ → ℂ), s) ∈ A := ⟨mem_ball_self hε, mem_ball_zero_iff.2 (hsn ▸ hrε)⟩
    have h0 : F (0, s) ≠ 0 := by
      show weierstrassPolynomial c (pointWithLast 0 s) ≠ 0
      rw [weierstrassPolynomial_pointWithLast_zero c hc0]
      exact pow_ne_zero _ (norm_ne_zero_iff.1 (hsn ▸ hr.ne'))
    exact (hFd _ hA).continuousAt.eventually_ne h0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff_ball.1 (hFne.and (ball_mem_nhds (0 : σ → ℂ) hε))

  let O₀ : Set ((σ → ℂ) × ℂ) := A ∩ F ⁻¹' {0}ᶜ
  have hO₀ : IsOpen O₀ := ContinuousOn.isOpen_inter_preimage
    (fun p hp => (hFd p hp).continuousAt.continuousWithinAt) (isOpen_ball.prod isOpen_ball) isOpen_compl_singleton
  have hmem₀ : ∀ z ∈ ball (0 : σ → ℂ) δ, ∀ s ∈ sphere (0 : ℂ) r, (z, s) ∈ O₀ := fun z hz s hs =>
    ⟨⟨(hδF z hz).2, mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hs).trans_lt hrε)⟩, (hδF z hz).1 s hs⟩

  let μ : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => ((fun i => p.1 (some i)), p.2)
  have hμ : Differentiable ℂ μ :=
    (differentiable_pi.2 fun i => by fun_prop).prodMk differentiable_snd
  let Φq : (Option σ → ℂ) × ℂ → ℂ := fun p => G (μ p) / (F (μ p) * (p.2 - p.1 none))
  let Oq : Set ((Option σ → ℂ) × ℂ) := μ ⁻¹' O₀ ∩ {p | p.2 - p.1 none ≠ 0}
  have hOq : IsOpen Oq := (hO₀.preimage hμ.continuous).inter (isOpen_ne_fun (by fun_prop) continuous_const)
  let Uq : Set (Option σ → ℂ) :=
    (fun x : Option σ → ℂ => fun i => x (some i)) ⁻¹' ball (0 : σ → ℂ) δ ∩ (fun x : Option σ → ℂ => x none) ⁻¹' ball (0 : ℂ) r
  have hUq : IsOpen Uq :=
    (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (continuous_apply none))
  have hΦq : DifferentiableOn ℂ Φq Oq := by
    rintro p ⟨⟨hA, hF⟩, hne⟩
    have hden : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => F (μ p) * (p.2 - p.1 none)) p :=
      ((hFd _ hA).comp p (hμ p)).mul (differentiableAt_snd.sub
        (by fun_prop : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => p.1 none) p))
    rw [show Φq = fun p => G (μ p) * (F (μ p) * (p.2 - p.1 none))⁻¹ from funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd _ hA).comp p (hμ p)).mul (hden.inv (mul_ne_zero hF hne))).differentiableWithinAt
  have hmemq : ∀ x ∈ Uq, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ Oq := by
    intro x hx s hs
    refine ⟨hmem₀ _ hx.1 s hs, ?_⟩
    show s - x none ≠ 0
    intro h
    have h1 := mem_sphere_zero_iff_norm.1 hs
    have h2 := mem_ball_zero_iff.1 hx.2
    rw [sub_eq_zero.1 h] at h1
    linarith
  have h0q : (0 : Option σ → ℂ) ∈ Uq := ⟨by exact Set.mem_preimage.mpr (mem_ball_self hδ), by exact Set.mem_preimage.mpr (mem_ball_self hr)⟩
  have hqan := hC (Option σ) Φq Oq Uq 0 r hr.le hOq hUq hΦq hmemq

  let Φa : Fin d → (σ → ℂ) × ℂ → ℂ := fun j p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j / F p
  have hΦa : ∀ j, DifferentiableOn ℂ (Φa j) O₀ := by
    intro j p hp
    have hP : DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => monicDifferenceCoeff (fun k => c k p.1) p.2 j) p := by
      show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ (d - 1 - (j : ℕ)) +
        ∑ k ∈ Finset.univ.filter (fun k : Fin d => (j : ℕ) < k), c k p.1 * p.2 ^ ((k : ℕ) - 1 - j)) p
      exact (differentiableAt_snd.pow _).add (DifferentiableAt.fun_sum fun k _ =>
        ((hcd p.1 hp.1.1 k).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))
    rw [show Φa j = fun p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j * (F p)⁻¹ from
      funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd p hp.1).mul hP).mul ((hFd p hp.1).inv hp.2)).differentiableWithinAt
  have haan := fun j => hC σ (Φa j) O₀ (ball 0 δ) 0 r hr.le hO₀ isOpen_ball (hΦa j) hmem₀
  refine ⟨fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φq (x, s),
    fun j z => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φa j (z, s),
    analyticAt_const.mul (hqan 0 h0q), fun j => analyticAt_const.mul (haan j 0 (mem_ball_self hδ)), ?_⟩
  filter_upwards [hUq.mem_nhds h0q] with x hx
  set z : σ → ℂ := fun i => x (some i) with hz
  set t : ℂ := x none with ht
  have hgx : g x = G (z, t) := congrArg g (pointWithLast_eta x).symm

  have hcau : (2 * π * I)⁻¹ • (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = G (z, t) := by
    refine DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun s => G (z, s)) ?_ hx.2
    refine DifferentiableOn.diffContOnCl_ball (U := ball 0 ε) (fun s hs => ?_) (closedBall_subset_ball hrε)
    exact ((hGd (z, s) ⟨(hδF z hx.1).2, hs⟩).comp s
      ((differentiableAt_const z).prodMk differentiableAt_id)).differentiableWithinAt

  have hpt : Set.EqOn (fun s => (s - t)⁻¹ • G (z, s))
      (fun s => weierstrassPolynomial c x * Φq (x, s) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := by
    intro s hs
    have hFs : F (z, s) ≠ 0 := (hδF z hx.1).1 s hs
    have hst : s - t ≠ 0 := (hmemq x hx s hs).2
    have key : F (z, s) - weierstrassPolynomial c x =
        (s - t) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) :=
      monic_sub_eq_mul_sum (fun k => c k z) s t
    have hsum : ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s) =
        G (z, s) / F (z, s) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show t ^ (j : ℕ) * (G (z, s) * monicDifferenceCoeff (fun k => c k z) s j / F (z, s)) = _
      ring
    have hP : ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) =
        (F (z, s) - weierstrassPolynomial c x) / (s - t) := by
      rw [key]
      field_simp
    show (s - t)⁻¹ • G (z, s) =
      weierstrassPolynomial c x * (G (z, s) / (F (z, s) * (s - t))) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)
    rw [hsum, hP, smul_eq_mul]
    field_simp
    ring
  have hcq : ContinuousOn (fun s => Φq (x, s)) (sphere (0 : ℂ) r) :=
    hΦq.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmemq x hx s hs
  have hca : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContinuousOn (fun s => t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := fun j _ => continuousOn_const.mul
    ((hΦa j).continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmem₀ z hx.1 s hs)
  have hint : (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) =
      weierstrassPolynomial c x * (∮ s in C(0, r), Φq (x, s)) +
        ∑ j : Fin d, t ^ (j : ℕ) * ∮ s in C(0, r), Φa j (z, s) := by
    have hi1 : CircleIntegrable (fun s => weierstrassPolynomial c x * Φq (x, s)) 0 r :=
      (continuousOn_const.mul hcq).circleIntegrable hr.le
    have hi2 : CircleIntegrable (fun s => ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) 0 r :=
      (continuousOn_finsetSum _ hca).circleIntegrable hr.le
    rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_add hi1 hi2,
      circleIntegral.integral_const_mul, circleIntegral_finset_sum _ _ hr.le hca]
    congr 1
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  rw [hgx, ← hcau, smul_eq_mul, hint, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CurveNormalisationQuotientLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    ringKrullDim (curveLocalRing I q) = 1 →
    Module.length (curveLocalRing I q)
        (curveNormalisation I q ⧸
          LinearMap.range (Algebra.linearMap (curveLocalRing I q) (curveNormalisation I q))) ≠ ⊤

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelGoodPointChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ), NormalModelDivisorGoodPoint M u d w → NormalDivisorChartAtPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y ≤
        r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

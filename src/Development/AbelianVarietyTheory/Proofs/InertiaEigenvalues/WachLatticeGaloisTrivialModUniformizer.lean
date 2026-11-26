module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulOfDvdRepr
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.GamModX

theorem full_of_std {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem shift_mem {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) (e y : ℤ → M) (he : e ∈ Λ) (u : L)
    (hy : ∀ k : ℤ, y k = u ^ k • e k - e k) :
    ∃ f ∈ Λ, ∀ j : ℤ, y j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h e).1 he
  refine ⟨fun k => y (k + 1), (h _).2 ⟨fun k => ?_, fun k hk => ?_⟩, fun j => by simp⟩
  · rw [hy]; exact D.sub_mem (D.smul_mem _ (h1 _)) (h1 _)
  · rw [hy]
    rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
    · simp [h2 _ h3]
    · simp [h3]

theorem conv_one {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : ℤ → M) :
    conv (1 : PowerSeries L) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem exists_smul_of_dvd_repr {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Fintype ι] (N : Submodule A M) (nb : Module.Basis ι A ↥N) (a : A) (z : ↥N)
    (hz : ∀ j, a ^ 1 ∣ nb.repr z j) : ∃ y ∈ N, (z : M) = a • y := by
  choose c hc using hz
  refine ⟨((∑ j, c j • nb j : ↥N) : M), Subtype.property _, ?_⟩
  have key : z = a • ∑ j, c j • nb j := by
    conv_lhs => rw [← nb.sum_repr z]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j, pow_one, mul_smul]
  exact congrArg Subtype.val key


set_option maxHeartbeats 1000000 in
theorem ex_of_val {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (m : ℕ)
    (hζ : ζ ^ (l ^ m) = 1) (g : (H.W K s LL h).Gam)
    (hg : (m : WithTop ℚ) ≤
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL)) - 1))
    (x : ↥((H.W K s LL h).N T)) (k : ℤ) :
    ex C h T i ζ ⟨_, (H.W K s LL h).N_Γ T g x x.2⟩ k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ g : ↥(OL LL))) ^ k • ex C h T i ζ x k := by
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
  have hjs : (j : WithTop ℚ) ≤ (m : WithTop ℚ) := by exact_mod_cast hj
  exact (C.C K s LL h).tie.levB_Γ T hT g i ζ ζ j 1
    (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ)
    (by rw [Nat.cast_one]; exact hjs.trans hg) (pow_one ζ).symm x
    ((H.W K s LL h).N_Γ T g x x.2) k


set_option maxHeartbeats 1000000 in
theorem sub_mem_X_of_val : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ g : W.Gam,
      ((s - 1 : ℕ) : WithTop ℚ) ≤
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) →
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT g hg x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  let x' : ↥(W.N T) := ⟨x, hx⟩
  let g' : ↥(W.N T) := ⟨_, W.N_Γ T g x hx⟩
  refine exists_smul_of_dvd_repr (W.N T) nb W.X (g' - x') fun j => ?_
  refine (GlobalTheory.T.wachWeierstrass_test_and_density D HW l K s LL h).2.1 1 _ fun i ζ hζ => ?_
  have hS := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT i ζ hζ
  have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    obtain ⟨j, -, hord⟩ :=
      (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
    exact ⟨j, hord ▸ IsPrimitiveRoot.orderOf ζ⟩
  have hI := (GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ hprim (full_of_std hS)).2 _ nb
  refine (hI.2.2 (g' - x') 1).1 ?_ j
  refine shift_mem hS (ex (Cm l) h T i ζ x') _ ?_
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) fun k => ?_
  · exact Submodule.subset_span ⟨1, x', (conv_one _).symm⟩
  · rw [← ex_of_val (Cm l) h T hT i ζ (s - 1) hζ g hg x' k]
    unfold ex
    rw [map_sub]
    rfl


set_option maxHeartbeats 1000000 in
theorem gam_mod_π_mod_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL), let W := (HW l).W K s LL h;
    ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
      (∀ g : W.Gam, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
      (∀ g : W.Gam, ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T g x - x = (letπ : AA K LL) • y) ∧
      ∀ x ∈ W.N T, ∃ y ∈ W.N T, W.γD T W.gam x - x = W.X • y := by
  intro D HW F Cm l _ K s LL h W T hT
  refine ⟨W.N_Γ T, W.N_π T, sub_mem_X_of_val D HW F Cm l K s LL h T hT W.gam ?_⟩
  have hg := W.gam_gen
  rw [(HW l).W_s] at hg
  have hs : ((s - 1 : ℕ) : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast Nat.sub_le s 1
  exact hs.trans hg.ge

end GlobalTheory.NL.GamModX
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachLatticeTrivialModUniformizer


set_option maxHeartbeats 1000000 in
theorem wachLattice_galois_trivial_mod_uniformizer : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P2 D HW F := by
  intro D HW F Cm l _ K s LL h T hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.NL.GamModX.gam_mod_π_mod_X D HW F Cm l K s LL h T hT
  refine ⟨(wach_gamma_stable_first _ T).1, (wach_gamma_stable_first _ T).2, fun x hx => ?_⟩
  obtain ⟨y, hy, e⟩ := h3 x hx
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.NL.WachLatticeTrivialModUniformizer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type),
    TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) →
    (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  intro l hl K bk ι tb w z t hsum hJ
  classical
  have hρ : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
    have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
    have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
    exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩
  have hinj : Function.Injective (toDisc l (bk.ev X) bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  have hiA : bk.iA = toDisc l (bk.ev X) bk.ρ₀ := rfl
  apply hinj
  rw [← hiA]
  have key : ∀ ε : ℝ, 0 < ε → ‖bk.iA z - bk.iA t‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := GlobalTheory.BSP.norm_toDisc_J_pow_small l K bk (Ainf l) bk.ev bk.ρ₀ hρ.1 hρ.2 ε hε
    obtain ⟨F, hF⟩ := hJ n
    have hev : ∀ᶠ G in Filter.atTop, ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := by
      have := (hsum : Filter.Tendsto _ _ _)
      have h2 := Metric.tendsto_nhds.1 this ε hε
      filter_upwards [h2] with G hG
      simpa [dist_eq_norm] using hG
    obtain ⟨G₀, hG₀⟩ := Filter.eventually_atTop.1 hev
    set G := F ∪ G₀
    have h1 : ‖bk.iA (z - ∑ i ∈ G, w i)‖ ≤ ε := hn _ (hF G Finset.subset_union_left)
    have h2 : ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := hG₀ G Finset.subset_union_right
    have hsplit : bk.iA z - bk.iA t = bk.iA (z - ∑ i ∈ G, w i) + (∑ i ∈ G, bk.iA (w i) - bk.iA t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]; abel
    rw [hsplit]
    calc _ ≤ ‖bk.iA (z - ∑ i ∈ G, w i)‖ + ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith
  have h0 : ‖bk.iA z - bk.iA t‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / 2) (by positivity)
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSumStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type), TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) → (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  first | exact @GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | exact GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic | (intros; apply GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.EquivOE

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_dvd_E : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) →
    bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) →
    ∀ i j, X i j ∈ bk.OE := by
  intro l _ K bk d d' S S' X hg hφ
  obtain ⟨u, hu, heu⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (not_dvd_E bk)
  have hA : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, S.A_mul]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : X = (u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a) •
      (S'.A.map bk.evW * X.map (frobW l) * S.A'.map bk.evW) := by
    rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm u, heu, one_pow, one_smul]
  intro i j
  refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => X p.1 p.2)
    (fun p q => u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a * bk.evW (S'.A q.1 p.1) * bk.evW (S.A' p.2 q.2))
    (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
  · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hu _) (bk.OE.pow_mem (evW_mem bk _) _))
      (evW_mem bk _)) (evW_mem bk _)
  · have h2 := congrFun (congrFun h1 q.1) q.2
    rw [h2, Fintype.sum_prod_type_right]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  · exact congrFun (congrFun (hg g h) q.1) q.2

end GlobalTheory.BSP.EquivOE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOEStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_phiModule_matrix_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) → bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) → ∀ i j, X i j ∈ bk.OE := by
  first | exact @GlobalTheory.BSP.EquivOE.main | exact GlobalTheory.BSP.EquivOE.main | (intros; apply GlobalTheory.BSP.EquivOE.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfIsBlockSum
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.ChiOneEnl

open GlobalTheory.IndefiniteRowSideFullHecke

theorem isConstituent_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h : BlockJumpCount.IsBlockSum D.nd i r ρ π) :
    BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (chiU D.nd i 1) (rO D.nd i r π) := by
  obtain ⟨e, he⟩ := h
  let c : Fin D.R.t := ⟨0, D.R.t_odd.pos⟩
  refine ⟨e.symm (0, Pi.single c 1), ?_, fun g => ?_⟩
  · intro h0
    have h1 := congrArg (fun u => (e u).2 c) h0
    simp at h1
  · apply e.injective
    have h2 := he g (e.symm (0, Pi.single c 1))
    rw [map_smul, e.apply_symm_apply]
    rw [e.apply_symm_apply] at h2
    refine h2.trans ?_
    refine Prod.ext ?_ ?_
    · simp
    · funext a
      by_cases ha : a = c
      · subst ha
        simp [c, Algebra.smul_def]
      · simp [ha]

theorem isCrys_chiE_of_constituent (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (L' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ L'.1)
    (hS : CrystallineSubrepresentation.SubCrys (Br.PD D.loc D.nbr i w hw) ↥L'.1) {n : ℕ}
    (χ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O i)ˣ) (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i))
    (h : BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i χ M)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL M))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (chiE D i w hw L' hL χ)) := by
  obtain ⟨v, hv, hg⟩ := h
  let f := (inc D i w hw L' hL).comp (Br.toLLK (D.nbr i w hw))
  let v' : Fin n → ↥L'.1 := fun a => f (v a)
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    funext a
    exact f.injective ((congrFun h0 a).trans (map_zero _).symm)
  have hf : ∀ x, f (toK D.nd i x) = inc D i w hw L' hL ((D.nbr i w hw).toLL x) := fun x =>
    congrArg (inc D i w hw L' hL) (WordJumpsCompare.toLLK_toK _ _ _ _ _)
  have key : ∀ g : Br.G D.nbr i w hw, (locE D i w hw L' hL M g).mulVec v' =
      ((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • v' := by
    intro g
    funext a
    have h1 := congrArg f (congrFun (hg (decS D.nd w (Br.iota D.nbr i w hw g))) a)
    have h2 : (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).mulVec v a =
        ∑ b, toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) * v b := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, Pi.smul_apply, smul_eq_mul, map_mul, hf] at h1
    simp only [map_mul, hf] at h1
    rw [Pi.smul_apply, smul_eq_mul]
    exact h1
  refine hS _ (matRep (locE D i w hw L' hL M)) _ _ (LinearMap.toSpanSingleton _ _ v') (fun g c => ?_)
    (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton _ hv')) hc
  change (((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • c) • v' =
    (locE D i w hw L' hL M g).mulVec (c • v')
  rw [Matrix.mulVec_smul, key, smul_smul, smul_eq_mul, mul_comm]

theorem chiOneE_of_isBlockSum (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π)))) :
    ChiOneE D i := by
  intro w hw L' hL
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (rO D.nd i r π))) :=
    GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _ (hc w hw)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _
      (isConstituent_of_isBlockSum D i r ρ π hs) hE)

end GlobalTheory.ChiOneEnl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

section IntegralSpan

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_filD_zero : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
  have h0 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← map_one (algebraMap (Per.AinfP l) (Per.BdRp l)),
      GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    simp
  have h1 := GlobalTheory.RingIface.alg_mem_FilD_nat l h0
  rwa [map_one, Nat.cast_zero] at h1

theorem algebraMap_mem_filD_zero (u : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filD_zero

theorem equivFinsuppOfBasisLeft_map_id {O B B' ι : Type} [CommRing O] [Algebra ℤ_[l] O]
    [CommRing B] [CommRing B'] [Algebra ℤ_[l] B] [Algebra ℤ_[l] B']
    [DecidableEq ι] (b : Module.Basis ι ℤ_[l] O) (g : B →ₐ[ℤ_[l]] B') (r : O ⊗[ℤ_[l]] B) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id O O) g r) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b r k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul o β => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem equivFinsuppOfBasisRight_map_id {O R R' M κ : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M]
    [DecidableEq κ] (b : Module.Basis κ O M) (f : R →ₐ[O] R') (w : R ⊗[O] M) (j : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f.toLinearMap LinearMap.id w) j =
      f (TensorProduct.equivFinsuppOfBasisRight b w j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mem_span_filD_zero_of_iotaO_eq {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (r : OB l O) (s : OD l O) (h : iotaO O C r = dRO l O s) :
    r ∈ Submodule.span O
      {u : OB l O | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l 0 ∧ u = (1 : O) ⊗ₜ[ℤ_[l]] β} := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hr : r = (TensorProduct.equivFinsuppOfBasisLeft b r).sum fun k β => b k ⊗ₜ[ℤ_[l]] β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hr, Finsupp.sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) ∈ Per.FilD l 0 := by
    have h1 := equivFinsuppOfBasisLeft_map_id b (iotaZ C) r k
    have h2 := equivFinsuppOfBasisLeft_map_id b (bdRpToBdR l) s k
    have h3 : Algebra.TensorProduct.map (AlgHom.id O O) (iotaZ C) r =
        Algebra.TensorProduct.map (AlgHom.id O O) (bdRpToBdR l) s := h
    rw [h3, h2] at h1
    have h4 : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) =
        algebraMap (Per.BdRp l) (Per.BdR l) (TensorProduct.equivFinsuppOfBasisLeft b s k) := h1.symm
    rw [h4]
    exact algebraMap_mem_filD_zero _
  have h5 : b k ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k) =
      b k • ((1 : O) ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hk, rfl⟩)

end IntegralSpan

theorem mem_span_filD_zero_of_integral : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
    (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T),
    TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) →
      w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T),
        C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ T C w hw
  classical
  obtain ⟨z, hz⟩ := hw
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  have hw' : w = (TensorProduct.equivFinsuppOfBasisRight bT w).sum fun j r => r ⊗ₜ[O] bT j := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hw', Finsupp.sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : iotaO O C (TensorProduct.equivFinsuppOfBasisRight bT w j) =
      dRO l O (TensorProduct.equivFinsuppOfBasisRight bT z j) := by
    rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
    exact (congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) hz).symm
  have hr := mem_span_filD_zero_of_iotaO_eq C _ _ hj
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk O (OB l O) ↥T.L.T).flip (bT j)) hr
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
  exact ⟨β, bT j, hβ, rfl⟩

end GlobalTheory.BKGal.HatVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T), TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) → w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | exact GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | (intros; apply GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem norm_toDisc_natPow_mul_le {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (n : ℕ)
    (w : A) : ‖toDisc l u ρ ((l : A) ^ n * w)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hm : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0 ∈
      ball l u ρ (((l : ℝ)⁻¹) ^ n) :=
    Submodule.subset_span ⟨n, 0, 0, by rw [pow_zero, pow_zero, mul_one, ← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow], rfl⟩
  have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ n * w) =
      w • (algebraMap A (PreDisc l u ρ) ((l : A) ^ n * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0) := by
    rw [Algebra.smul_def, pow_zero, pow_zero, mul_one, mul_one, ← map_mul, mul_comm]
  show ‖ofPre l u ρ (algebraMap A _ _)‖ ≤ _
  rw [norm_ofPre, e]
  exact gauge_le l u ρ (by positivity) (Submodule.smul_mem _ w hm)

theorem BK.ρ₀_mem_Ioo_zero_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    rw [neg_lt_zero]; positivity

theorem seed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdicStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BSP.seed_module_lAdic_closed | exact GlobalTheory.BSP.seed_module_lAdic_closed | (intros; apply GlobalTheory.BSP.seed_module_lAdic_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriod
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightAprime

theorem dvd_of_dvd_prime_pow_mul {R : Type} [CommRing R] [IsDomain R] {p a b : R} (hp : Prime p)
    (ha : ¬ p ∣ a) : ∀ n : ℕ, a ∣ p ^ n * b → a ∣ b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro h
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩
    obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha
    refine ih ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩
    linear_combination hx

theorem C_dvd_iff {R : Type} [CommRing R] (p : R) (f : R⟦X⟧) :
    C p ∣ f ↔ ∀ n, p ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun n => (h n).choose, ?_⟩
    ext n
    rw [coeff_C_mul, coeff_mk]
    exact (h n).choose_spec

theorem prime_C {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Prime (C p : R⟦X⟧) := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let q : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk _
  have key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0 := by
    intro f
    rw [C_dvd_iff]
    constructor
    · intro h; ext n
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))
    · intro h n
      have := congrArg (coeff n) h
      rw [coeff_map, map_zero] at this
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  refine ⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩
  · simpa using h.map (constantCoeff (R := R))
  · intro f g hfg
    rw [key, key]
    rw [key, map_mul] at hfg
    exact mul_eq_zero.1 hfg

theorem prime_l {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] : Prime (l : (Wq l a)⟦X⟧) := by
  have h : Prime (l : Wq l a) := (WittVector.irreducible l).prime
  have := prime_C h
  simpa using this

end GlobalTheory.BSP.HeightAprime

namespace GlobalTheory.BSP.HeightAprime

variable {l : ℕ} [hl : Fact l.Prime]

theorem not_l_dvd_det {K : FinExt l} (bk : BK K) {d : ℕ} (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A : Matrix (Fin d) (Fin d) bk.S) (hY : IsUnit (Y.map (inclW l)))
    (hφ : Y.map WittVector.frobenius = Y * A.map bk.ev) : ¬ (l : bk.S) ∣ A.det := by
  rintro ⟨t, ht⟩
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h0 := congrArg WittVector.constantCoeff h2
  rw [ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero] at h0
  have hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l :=
    WittVector.coeff_frobenius_charP l _ 0
  have hz : Y.det.coeff 0 = 0 := by
    have : WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0 := rfl
    rw [this, hc] at h0
    exact pow_eq_zero_iff hl.out.ne_zero |>.1 h0
  have hu : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  have hu0 := hu.map (WittVector.constantCoeff (p := l) (R := Cb l))
  have : WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0 := rfl
  rw [this, inclW, WittVector.map_coeff, hz, map_zero] at hu0
  exact not_isUnit_zero hu0

end GlobalTheory.BSP.HeightAprime

theorem GlobalTheory.BSP.HeightAprime.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  intro l _ K bk τ hτ d Y S' A k M hY hYS hφ
  have h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d := by
    rw [← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) =
      bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d) := by
    have := congrArg WittVector.frobenius h1
    rw [map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1] at this
    rw [map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]
    linear_combination this
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (M * d)
  set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)
  have hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d)) := fun i => by
    have := congrArg (TB.c i) h3
    rw [TB.c_mul, TB.c_mul] at this
    exact ⟨_, this.symm⟩
  have hdvd : A.det ∣ c * (l : bk.S) ^ r := by
    refine Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩; exact hdiv i
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact dvd_add hx hy
    · intro a x _ hx; rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx a
  have hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
    have e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
      simp only [c]; ring
    rwa [e] at hdvd
  obtain ⟨q, hq⟩ := GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a)
    (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'
  refine ⟨M * d, q • A.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriodStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  first | exact @GlobalTheory.BSP.HeightAprime.main | exact GlobalTheory.BSP.HeightAprime.main | (intros; apply GlobalTheory.BSP.HeightAprime.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.GLq.Leibniz

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, wh ψ (f j) := by
  unfold wh tr
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_mul_const (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_gl_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Subsingleton.elim _ _)
  have huniv : (Finset.univ : Finset (Gn g 0)) = {1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hsub x
  have hP : IsUniUp ((1 : Gn g 0) : Mt g 0) := fun a _ => a.elim0
  unfold wh tr eU eDat
  rw [huniv, Finset.sum_singleton]
  rw [Finset.filter_singleton, if_pos hP, Finset.sum_singleton, Finset.card_singleton]
  simp

theorem degL_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) :
    degL ((I.sort (· ≤ ·)).map L.get) = ∑ j ∈ I, (L.get j).1 := by
  unfold degL
  rw [List.map_map]
  have := Finset.sort_eq I (· ≤ ·)
  rw [Finset.sum_eq_multiset_sum, ← this, Multiset.map_coe, Multiset.sum_coe]
  rfl

theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  have h := degL_sort_map L Finset.univ
  rw [Fin.sort_univ, List.map_get_finRange] at h
  exact h

theorem mem_of_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) {p : Pc g}
    (hp : p ∈ (I.sort (· ≤ ·)).map L.get) : p ∈ L := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  exact List.get_mem L j

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (hcL L (degL L)) = 1 := by
  intro L
  induction L with
  | nil => intro _; exact wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL' q hq).1.2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.1.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul]
      rw [wh_mul_const, ih hL', hp.2, one_mul]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem wh_hcL_of_deg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g)) (n : ℕ) (hn : degL L = n)
    (hL : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L n) = 1 := by
  subst hn
  exact wh_hcL ψ hψ L hL

theorem main : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ),
    degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) →
      wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  intro g _ ψ hψ L n i hn hi hL
  refine ⟨?_, wh_hcL_of_deg ψ hψ L n hn hL⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hcusp : ∀ p ∈ L, IsCusp p.2 := fun p hp => (hL p hp).1
  have htot : ∑ j : Fin L.length, (L.get j).1 = i + k := by rw [← degL_eq_sum]; exact hn
  have hsub : ∀ (I : Finset (Fin L.length)), ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2 ∧ wh ψ p.2 = 1 :=
    fun I p hp => hL p (mem_of_sort_map L I hp)
  have hB : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    refine wh_hcL_of_deg ψ hψ _ k ?_ (hsub Iᶜ)
    rw [degL_sort_map]
    have := Finset.sum_compl_add_sum I (fun j => (L.get j).1)
    omega
  have hA : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((I.sort (· ≤ ·)).map L.get) i) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    exact wh_hcL_of_deg ψ hψ _ i (by rw [degL_sort_map]; exact hI.2) (hsub I)
  have key : ∀ b, b = k → ∀ h : Gn g i, wh ψ (res i b (hcL L (i + k)) h) =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) := by
    intro b hb h
    subst hb
    have hr : res i b (hcL L (i + b)) h = fun y => ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i),
          hcL ((I.sort (· ≤ ·)).map L.get) i h * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y :=
      funext fun y => GlobalTheory.GLq.ResCuspProd.main g L i b hn hcusp h y
    rw [hr, wh_sum]
    exact Finset.sum_congr rfl fun I _ => wh_const_mul ψ _ _
  have hder : der ψ i (hcL L (i + k)) = fun h =>
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) :=
    funext fun h => key (i + k - i) (by omega) h
  rw [hder, wh_sum, Finset.sum_congr rfl fun I hI => by rw [wh_mul_const, hA I hI, hB I hI, one_mul]]
  simp

end GlobalTheory.GLq.Leibniz
end

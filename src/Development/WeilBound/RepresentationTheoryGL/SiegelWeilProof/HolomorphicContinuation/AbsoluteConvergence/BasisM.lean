module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FirstCountableBlockMatrices
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisA
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem continuous_mR : Continuous (fun g : GR n => mR g) := by
  unfold mR; fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 :=
  IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit)

theorem continuous_group_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_group_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  unfold F0 f0
  refine Continuous.mul ((continuous_mR.matrix_det).zpow₀ e fun g => Or.inl (det_mR_ne g)) (Continuous.mul ?_ ?_)
  · exact ((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).1
  · exact ((continuous_second_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).2

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  have : (u1 (mR g)).det ≠ 0 := (hD n g).1
  positivity

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  refine Continuous.inv₀ ?_ fun g => ?_
  · exact (((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).norm).pow 2
  · have : (u1 (mR g)).det ≠ 0 := (hD n g).1
    positivity

theorem hLoc_one : hLoc (1 : GR n) = 1 := by
  have h1 : u1 (1 : M2 n) = 1 := by
    ext i j
    simp [u1, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  simp [hLoc, mR_one, h1]

theorem hLoc_K (hM : Mult) (k : GR n) (hk : k ∈ KR n) : hLoc k = 1 := by
  have := ((hM n 0 0 0).1 1 k hk).2
  rw [one_mul, hLoc_one] at this
  exact this

def uSet (n : ℕ) : Set (M2 n) := {u | uᴴ * u = 1 ∧ InG u}

theorem isCompact_uSet (n : ℕ) : IsCompact (uSet n) := by
  have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · change IsClosed ({u : M2 n | uᴴ * u = 1} ∩ {u : M2 n | InG u})
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq ((continuous_id : Continuous (fun u : M2 n => u)).matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq (((continuous_id : Continuous (fun u : M2 n => u)).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
  · intro u hu
    have hU : u ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hu.1
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hU i j

def toK (u : uSet n) : KR n :=
  ⟨⟨⟨u.1, u.1ᴴ, mul_eq_one_comm.1 u.2.1, u.2.1⟩, u.2.2⟩, ⟨u.2.2, u.2.1⟩⟩

theorem continuous_toK : Continuous (toK (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

instance compactKR (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  refine ⟨?_⟩
  have : (univ : Set (KR n)) = toK '' univ := by
    ext k
    simp only [mem_univ, mem_image, true_and, true_iff]
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl
  rw [this]
  exact isCompact_univ.image continuous_toK

theorem exists_pts {X : Type*} : ∀ (N : ℕ) (f : Fin N → X → ℂ), LinearIndependent ℂ f →
    ∃ x : Fin N → X, (Matrix.of fun j l => f j (x l)).det ≠ 0 := by
  intro N
  induction N with
  | zero => intro f _; exact ⟨Fin.elim0, by simp⟩
  | succ N ih =>
    intro f hf
    obtain ⟨x', hx'⟩ := ih (fun j => f (Fin.castSucc j)) (hf.comp _ (Fin.castSucc_injective N))
    let c : Fin (N + 1) → ℂ := fun i => (-1) ^ ((i : ℕ) + N) * (Matrix.of fun a b => f (i.succAbove a) (x' b)).det
    have hdet : ∀ y : X, (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).det =
        ∑ i, c i * f i y := by
      intro y
      rw [Matrix.det_succ_column _ (Fin.last N)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).submatrix i.succAbove
          (Fin.last N).succAbove = Matrix.of fun a b => f (i.succAbove a) (x' b) := by
        ext a b
        simp [Fin.succAbove_last]
      rw [hs]
      simp only [c, Matrix.of_apply, Fin.lastCases_last, Fin.val_last]
      ring
    by_contra hcon
    push Not at hcon
    have key : ∑ i, c i • f i = 0 := by
      funext y
      have h := hcon (Fin.lastCases (motive := fun _ => X) y x')
      rw [hdet y] at h
      simpa [Finset.sum_apply] using h
    have h0 := Fintype.linearIndependent_iff.1 hf c key (Fin.last N)
    have hc : c (Fin.last N) ≠ 0 := by
      simp only [c, Fin.val_last, Fin.succAbove_last]
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      simpa using hx'
    exact hc h0

end PositivityTheory.Rg.Sw.AbsSt.BasisPf
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem flatEq_of (hI : Iwa) : FlatEq := by
  intro m n ε c t p q e sL ρ hL Q Q' hQ y
  obtain ⟨pp, k, hp, hk, rfl⟩ := hI n y
  rw [hL.law Q pp k hp, hL.law Q' pp k hp, hQ k hk]

variable {m n : ℕ}

def secK (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) : PX m n →ₗ[ℂ] C(KR n, ℂ) where
  toFun Q := ⟨fun k => sL Q (k : GR n), (hc Q).comp continuous_subtype_val⟩
  map_add' Q Q' := by ext k; simp
  map_smul' a Q := by ext k; simp

theorem secK_apply (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (hc : ∀ Q, Continuous (sL Q)) (Q : PX m n) (k : KR n) :
    secK sL hc Q k = sL Q (k : GR n) := rfl

theorem bij_toK : Function.Bijective (toK (n := n)) := by
  constructor
  · intro u v h
    apply Subtype.ext
    have := congrArg (fun k : KR n => ((k : GR n) : GL (Fin n ⊕ Fin n) ℂ).1) h
    exact this
  · intro k
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance t2KR : T2Space (KR n) := inferInstance

def homeoK : uSet n ≃ₜ KR n :=
  haveI : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  continuous_toK.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bij_toK)

instance firstCountableBlockMatrices : FirstCountableTopology (M2 n) := by
  show FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ); infer_instance

instance fcKR : FirstCountableTopology (KR n) :=
  (homeoK (n := n)).symm.isInducing.firstCountableTopology

section Op

variable [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) [IsFiniteMeasure ν]

theorem integrable_of_cont {f : KR n → ℂ} (hf : Continuous f) : Integrable f ν :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

def piFun (κ : C(KR n, ℂ)) (h : C(KR n, ℂ)) : C(KR n, ℂ) :=
  ⟨fun k' => ∫ k, κ k * h (k' * k) ∂ν, by
    refine continuous_of_dominated (bound := fun _ => ‖κ‖ * ‖h‖) (fun k' => ?_) (fun k' => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun k => ?_)
    · exact (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun k => ?_
      rw [norm_mul]
      exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    exact continuous_const.mul (h.continuous.comp (continuous_id.mul continuous_const))⟩

theorem piFun_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piFun ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

def piL (κ : C(KR n, ℂ)) : C(KR n, ℂ) →L[ℂ] C(KR n, ℂ) :=
  LinearMap.mkContinuous
    { toFun := piFun ν κ
      map_add' := fun h h' => by
        ext k'
        simp only [piFun_apply, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_of_cont ν (κ.continuous.mul (h.continuous.comp (continuous_const.mul continuous_id))))
          (integrable_of_cont ν (κ.continuous.mul (h'.continuous.comp (continuous_const.mul continuous_id))))
      map_smul' := fun a h => by
        ext k'
        simp only [piFun_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext k; ring }
    (‖κ‖ * ν.real univ) fun h => by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k' => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, piFun_apply]
      calc ‖∫ k, κ k * h (k' * k) ∂ν‖ ≤ (‖κ‖ * ‖h‖) * ν.real univ := by
            refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (κ.norm_coe_le_norm k) (h.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
        _ = ‖κ‖ * ν.real univ * ‖h‖ := by ring

theorem piL_apply (κ h : C(KR n, ℂ)) (k' : KR n) : piL ν κ h k' = ∫ k, κ k * h (k' * k) ∂ν := rfl

end Op

end PositivityTheory.Rg.Sw.AbsSt.BasisPf
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem basis_of (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWρ ν κ hν hκ ha hb P hP
  have := hν
  have := hW
  let sK := secK sL hL.cont
  let V : Submodule ℂ C(KR n, ℂ) := W.map sK
  let κC : C(KR n, ℂ) := ⟨κ, hκ⟩
  have hF0c := continuous_weight_factor (n := n) hD p q e

  have hflat : ∀ y : GR n, ∃ Q ∈ W, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y' := by
    intro y
    obtain ⟨Q, hQW, hQ⟩ := hb 0 (fun g => F0 p q e (g * y)) (hF0c.comp (continuous_id.mul continuous_const))
      (fun y0 g hy0 => by
        simp only [Complex.cpow_zero, one_mul]
        rw [mul_assoc, ((hM n p q e).2 y0 (g * y) hy0).1])
    exact ⟨Q, hQW, fun y' => by simpa using hQ y'⟩
  choose QF hQFW hQF using hflat
  let v : GR n → V := fun y => ⟨sK (QF y), Submodule.mem_map_of_mem (hQFW y)⟩
  have hpi_v : ∀ y (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → piL ν κC h = sK (QF y) := by
    intro y h hh
    ext k'
    rw [piL_apply, secK_apply, ← hQF y (k' : GR n)]
    congr 1; funext k
    rw [hh]; simp [κC, mul_assoc]
  have hpi_W : ∀ Q ∈ W, piL ν κC (sK Q) = sK Q := by
    intro Q hQ
    ext k'
    rw [piL_apply, secK_apply, ← ha Q hQ (k' : GR n)]
    rfl

  have hspan : Submodule.span ℂ (range v) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span ℂ (range v) < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨ℓ, hℓ0, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    obtain ⟨pr, hpr⟩ := Submodule.ClosedComplemented.of_finiteDimensional V
    let ℓc : V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ℓ
    let L : C(KR n, ℂ) →L[ℂ] ℂ := ℓc.comp (pr.comp (piL ν κC))
    have hLv : ∀ (y : GR n) (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0 := by
      intro y h hh
      have e1 : L h = ℓ (pr (piL ν κC h)) := rfl
      rw [e1, hpi_v y h hh]
      have e2 : pr (sK (QF y)) = v y := hpr (v y)
      rw [e2]
      have hmem : v y ∈ Submodule.span ℂ (range v) := Submodule.subset_span ⟨y, rfl⟩
      have : ℓ (v y) ∈ (Submodule.span ℂ (range v)).map ℓ := Submodule.mem_map_of_mem hmem
      rw [hℓS] at this
      simpa using this
    apply hℓ0
    ext ⟨x, hx⟩
    obtain ⟨Q, hQ, rfl⟩ := hx
    have h0 := hC m n ε c t p q e sL ρ hL L hLv Q (sK Q) (fun k => rfl)
    have e1 : L (sK Q) = ℓ (pr (piL ν κC (sK Q))) := rfl
    rw [e1, hpi_W Q hQ] at h0
    have e2 : pr (sK Q) = ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ := hpr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩
    rw [e2] at h0
    simpa using h0

  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (range v)
  have hs_top : ⊤ ≤ Submodule.span ℂ (range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hs_span, hspan]
  let bV := Module.Basis.mk hs_li hs_top
  have : Finite s := Module.Finite.finite_basis bV
  have : Fintype s := Fintype.ofFinite s
  let N := Fintype.card s
  let b : Module.Basis (Fin N) ℂ V := bV.reindex (Fintype.equivFin s)
  have hbv : ∀ i, ∃ y, v y = b i := by
    intro i
    have hb' : (b i : V) = ((Fintype.equivFin s).symm i : V) := by
      simp [b, bV]
    rw [hb']
    exact hs_sub ((Fintype.equivFin s).symm i).2
  choose yy hyy using hbv
  let QQ : Fin N → PX m n := fun i => QF (yy i)
  have hQQ : ∀ i (k : KR n), ((b i : V) : C(KR n, ℂ)) k = sL (QQ i) (k : GR n) := by
    intro i k; rw [← hyy i]; rfl
  have hcoord : ∀ Q (hQ : Q ∈ W) (k : KR n), sL Q (k : GR n) =
      ∑ j, b.repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ j * sL (QQ j) (k : GR n) := by
    intro Q hQ k
    have h := congrArg (fun x : V => ((x : C(KR n, ℂ)) k)) (b.sum_repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ] at h
    rw [h]; rfl
  have hsum_sL : ∀ (d : Fin N → ℂ) (y : GR n), sL (∑ j, d j • QQ j) y = ∑ j, d j * sL (QQ j) y := by
    intro d y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply]
  let cc : Fin N → ℂ := fun j => b.repr ⟨sK P, Submodule.mem_map_of_mem hP⟩ j
  have hPsum : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL P (∑ j, cc j • QQ j) (fun k hk => by
      rw [hcoord P hP ⟨k, hk⟩, hsum_sL]) y, hsum_sL]

  let f : Fin N → KR n → ℂ := fun j k => sL (QQ j) (k : GR n)
  have hfli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : ∑ j, g j • b j = 0 := by
      apply Subtype.ext
      ext k
      have := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ, Submodule.coe_zero, ContinuousMap.zero_apply]
      exact this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g h2
  obtain ⟨kk, hkk⟩ := exists_pts N f hfli
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j l => f j (kk l)
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hkk
  let Ev : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Matrix.of fun i l =>
    ∫ k, κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)) ∂ν
  let M : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Ev w * A⁻¹
  have hEv0 : Ev 0 = A := by
    ext i l
    simp only [Ev, A, f, Matrix.of_apply, Complex.cpow_zero, one_mul]
    exact hQF (yy i) (kk l)
  have hM0 : M 0 = 1 := by
    show Ev 0 * A⁻¹ = 1
    rw [hEv0]; exact Matrix.mul_nonsing_inv A hA
  have hEvd : ∀ i l, Differentiable ℂ (fun w => Ev w i l) := by
    intro i l
    have hcg : Continuous (fun k : KR n => (kk l : GR n) * (k : GR n) * yy i) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hpos : ∀ k : KR n, 0 < hLoc ((kk l : GR n) * (k : GR n) * yy i) := fun k => hLoc_pos hD _
    have h := (hH (KR n) ν univ isCompact_univ (by simp) univ
      (fun k w => κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)))
      isOpen_univ ?_ ?_).1
    · exact differentiableOn_univ.1 h
    · refine Continuous.continuousOn ?_
      refine (hκ.comp continuous_fst).mul (Continuous.mul ?_ (hF0c.comp (hcg.comp continuous_fst)))
      exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp (hcg.comp continuous_fst)))
        continuous_snd (fun y => Complex.ofReal_mem_slitPlane.2 (hpos y.1))
    · intro k _
      have hne : ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
      exact ((((differentiable_id.const_cpow (Or.inl hne)).mul_const _).const_mul _)).differentiableOn
  have hMd : ∀ i j, Differentiable ℂ (fun w => M w i j) := by
    intro i j
    show Differentiable ℂ (fun w => (Ev w * A⁻¹) i j)
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun l _ => (hEvd i l).mul_const _
  refine ⟨N, yy, QQ, cc, M, fun j => hQFW (yy j), hPsum, hM0, hMd, fun i y' => hQF (yy i) y', ?_⟩
  intro w i y'
  let fw : GR n → ℂ := fun g => (hLoc (g * yy i) : ℂ) ^ w * F0 p q e (g * yy i)
  have hfwc : Continuous fw := by
    have hg : Continuous (fun g : GR n => g * yy i) := continuous_id.mul continuous_const
    refine Continuous.mul ?_ (hF0c.comp hg)
    exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hg)) continuous_const
      (fun g => Complex.ofReal_mem_slitPlane.2 (hLoc_pos hD _))
  have hfwlaw : ∀ (y0 g : GR n), (mR y0).toBlocks₂₁ = 0 → fw (y0 * g) = (hLoc y0 : ℂ) ^ w * F0 p q e y0 * fw g := by
    intro y0 g hy0
    simp only [fw]
    rw [mul_assoc y0 g (yy i)]
    obtain ⟨h1, h2⟩ := (hM n p q e).2 y0 (g * yy i) hy0
    rw [h1, h2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (hLoc_pos hD y0).le (hLoc_pos hD _).le]
    ring
  obtain ⟨Qw, hQwW, hQw⟩ := hb w fw hfwc hfwlaw
  let a := b.repr ⟨sK Qw, Submodule.mem_map_of_mem hQwW⟩
  have hEva : ∀ l, Ev w i l = ∑ j, a j * A j l := by
    intro l
    have h1 := hQw (kk l : GR n)
    rw [hLoc_K hM _ (kk l).2] at h1
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h1
    rw [hcoord Qw hQwW (kk l)] at h1
    simp only [Ev, A, f, Matrix.of_apply]
    rw [← h1]
  have hrow : (fun l => Ev w i l) = Matrix.vecMul a A := by
    funext l; rw [hEva l]; simp [Matrix.vecMul, dotProduct]
  have hMa : ∀ j, M w i j = a j := by
    intro j
    have e1 : M w i j = Matrix.vecMul (fun l => Ev w i l) A⁻¹ j := by
      simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [e1, hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
  have hflatw : ∀ y, sL Qw y = ∑ j, M w i j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL Qw (∑ j, M w i j • QQ j) (fun k hk => by
      rw [hcoord Qw hQwW ⟨k, hk⟩, hsum_sL]
      simp only [hMa]; rfl) y, hsum_sL]
  rw [show (∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν) =
      ∫ k, κ k * fw (y' * (k : GR n)) ∂ν from rfl, hQw y', hflatw]

end PositivityTheory.Rg.Sw.AbsSt.BasisPf

namespace PositivityTheory.Rg.Sw.AbsSt

theorem basis (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis :=
  BasisPf.basis_of hI hD hM hC hH

end PositivityTheory.Rg.Sw.AbsSt

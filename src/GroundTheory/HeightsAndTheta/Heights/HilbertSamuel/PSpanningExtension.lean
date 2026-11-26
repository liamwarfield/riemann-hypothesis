module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IdxAssembleStA

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module Set

theorem SpanningExtension.proof : SpanningExtension.Statement := by
  intro V _ _ _ ι _ v S hv hS
  classical
  set s : Set V := range v with hs_def
  have hs : LinearIndepOn ℝ id s := (linearIndepOn_id_range_iff hv.injective).mpr hv
  have hst : s ⊆ s ∪ S := subset_union_left
  set b := hs.extend hst with hb_def
  have hsb : s ⊆ b := hs.subset_extend hst
  have hbt : b ⊆ s ∪ S := hs.extend_subset hst
  have hbli : LinearIndependent ℝ (fun x : b => (x : V)) := hs.linearIndepOn_extend hst
  have hspan : ⊤ ≤ Submodule.span ℝ (range (fun x : b => (x : V))) := by
    rw [Subtype.range_coe, ← hS]
    exact Submodule.span_le.2 (subset_union_right.trans (hs.subset_span_extend hst))
  let B := Basis.mk hbli hspan
  have hcard_b : Nat.card b = finrank ℝ V := (finrank_eq_nat_card_basis B).symm
  have : Finite b := Module.Finite.finite_basis B
  have hbfin : b.Finite := toFinite b
  have hcard_s : s.ncard = Fintype.card ι := by
    rw [hs_def, ncard_range_of_injective hv.injective, Nat.card_eq_fintype_card]
  have hk : Nat.card (b \ s : Set V) = finrank ℝ V - Fintype.card ι := by
    rw [Nat.card_coe_set_eq, ncard_sdiff hsb (hbfin.subset hsb), ← hcard_s, ← Nat.card_coe_set_eq,
      hcard_b]
  let e : (b \ s : Set V) ≃ Fin (finrank ℝ V - Fintype.card ι) := Finite.equivFinOfCardEq hk
  let w : Fin (finrank ℝ V - Fintype.card ι) → V := fun j => (e.symm j : V)
  have hw_mem : ∀ j, w j ∈ b \ s := fun j => (e.symm j).2
  refine ⟨w, fun j => ?_, ?_⟩
  · obtain ⟨hb, hns⟩ := hw_mem j
    rcases hbt hb with h | h
    · exact absurd h hns
    · exact h
  · let f : ι ⊕ Fin (finrank ℝ V - Fintype.card ι) → b :=
      Sum.elim (fun i => ⟨v i, hsb (mem_range_self i)⟩) (fun j => ⟨w j, (hw_mem j).1⟩)
    have hf : Function.Injective f := by
      rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [hv.injective h]
      · exact absurd (h ▸ mem_range_self i) (hw_mem j').2
      · exact absurd (h ▸ mem_range_self i') (hw_mem j).2
      · rw [e.symm.injective (Subtype.ext h)]
    have : Sum.elim v w = (fun x : b => (x : V)) ∘ f := by
      funext x; rcases x with i | j <;> rfl
    rw [this]
    exact hbli.comp f hf

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem EmbeddingPieces.proof (hA : PiecesAdditive.Statement) (hD : PieceDegree.Statement) :
    EmbeddingPieces.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D L c w hP hbir hL hex hw
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg => EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hind : ∀ (d : (F →+* ℂ) → ℝ), ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg, LiesOver y sg z →
      ∑ s, d s * (S s).indicator (fun _ => (1 : ℝ)) z = d sg := by
    intro d z hz sg hsg
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  have hwL : ptsIntegral (mCoordIdeal y) (pot L) w = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, c s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind c z hz sg hsg]
    exact (hw z hz sg hsg).self_of_nhds
  have h1 : ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1) = ptsIntegral (mCoordIdeal y) (pot L)
      (fun z => ∑ s, (fun _ => (1 : ℝ)) s * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    rw [hind _ z hz sg hsg]
  rw [hwL, h1, hA K ι _ D L (F →+* ℂ) S c hP hL hSc hSs hex',
    hA K ι _ D L (F →+* ℂ) S (fun _ => 1) hP hL hSc hSs hex']
  rcases isEmpty_or_nonempty (F →+* ℂ) with he | ⟨⟨s0⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hI : ∀ s, ptsIntegral (mCoordIdeal y) (pot L) ((S s).indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot L) ((S s0).indicator fun _ => (1 : ℝ)) :=
      fun s => hD K ι Ω F y D L s s0 hP hbir hL hex
    simp only [hI, ← Finset.sum_mul, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem LiftAtPrime.proof (hC : GeneratedPow.Statement) (hA : FibreSectionLift.Statement)
    (hB : FibreRelLift.Statement) : LiftAtPrime.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N p hY hp hN
  obtain ⟨q, hq, hgen, hvan⟩ := hN
  obtain ⟨t₀, ht₀⟩ := hvan 0
  refine ⟨q, t₀, hq, fun t ht => ?_⟩
  have hga : KH.GeneratedV (ZMod p) (fibreIdeal p y) ((t * q) • N) := by
    have h := hC (ZMod p) K ι (fibreIdeal p y) (q • N) t hgen
    rwa [smul_smul] at h
  have hH1 : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) ((t * q) • N) 1) := by
    have h := ht₀ t ht
    rwa [zero_add] at h
  have hfi : fibreIdeal p y = GenOnFibres.idealOver y (ZMod p) := rfl
  rw [hfi] at hga hH1
  choose r z u hz hu hrel using hga
  have hlift : ∀ I j, ∃ s ∈ chartLat y ((t * q) • N) 1,
      GenOnFibres.secCoch y (ZMod p) s ((t * q) • N) = z I j :=
    fun I j => hA K ι Ω y D p ((t * q) • N) hY hp hH1 (z I j) (hz I j)
  choose s hs hsz using hlift
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  have : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Σ I, Fin (r I))).symm
  refine ⟨Fintype.card (Σ I, Fin (r I)), fun j => s (e j).1 (e j).2, fun j => hs _ _, fun c hc => ?_⟩
  let J : KH.Cell K ι 0 := ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hJ : GenOnFibres.cellChart J = c :=
    funext fun k => Finset.mem_singleton.mp (GenOnFibres.cellChart_mem J k)
  have hrelJ : ∑ j, u J j * GenOnFibres.secCoch y (ZMod p) (s J j) ((t * q) • N) J = 1 := by
    rw [← hrel J]
    exact Finset.sum_congr rfl fun j _ => by rw [hsz J j]
  obtain ⟨u', v, hu', hv, hsum⟩ :=
    hB K ι Ω y p ((t * q) • N) (r J) (s J) J (u J) (hs J) (by rw [hJ]; exact hc) (hu J) hrelJ
  rw [hJ] at hu' hv hsum
  let U : (Σ I, Fin (r I)) → Ω := fun x => if h : x.1 = J then u' (Fin.cast (congrArg r h) x.2) else 0
  refine ⟨fun j => U (e j), v, fun j => ?_, hv, ?_⟩
  · simp only [U]
    split_ifs
    · exact hu' _
    · exact zero_mem _
  · rw [← hsum]
    congr 1
    rw [e.sum_comp (fun x => U x * (s x.1 x.2 * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))),
      Fintype.sum_sigma, Finset.sum_eq_single J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [U]
    · intro I _ hI
      exact Finset.sum_eq_zero fun j _ => by simp [U, hI]
    · intro h
      exact absurd (Finset.mem_univ J) h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiposTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace GramContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem det_gram_le_prod {α : Type*} [Fintype α] [DecidableEq α] (y : α → V) :
    (Matrix.gram ℝ y).det ≤ ∏ a, ‖y a‖ ^ 2 := by
  by_cases hy : LinearIndependent ℝ y
  · let e := Fintype.equivFin α
    have h := HadamardGramBound.det_gram_le_prod_norm_sq (y ∘ e.symm) (hy.comp _ e.symm.injective)
    have hg : Matrix.gram ℝ (y ∘ e.symm) = (Matrix.gram ℝ y).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.gram_apply]
    rw [hg, Matrix.det_submatrix_equiv_self] at h
    rwa [Fintype.prod_equiv e.symm (fun i => ‖(y ∘ e.symm) i‖ ^ 2) (fun a => ‖y a‖ ^ 2) (fun _ => rfl)] at h
  · have h0 : (Matrix.gram ℝ y).det = 0 := by
      by_contra h; exact hy (Matrix.det_gram_ne_zero_iff_linearIndependent.mp h)
    rw [h0]; exact Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem gram_comb {α : Type*} [Fintype α] (M : Matrix α α ℝ) (y : α → V) :
    Matrix.gram ℝ (fun a => ∑ b, M a b • y b) = M * Matrix.gram ℝ y * M.transpose := by
  ext i k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GramContraction

theorem GramContraction.proof : GramContraction.Statement := by
  intro ι κ _ _ _ _ V _ _ Ψ u w hΨ
  let e := EuclideanSpace.basisFun ι ℝ
  let U : Matrix ι ι ℝ := Matrix.of fun i j => u i j
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks U 0 0 1
  let y : ι ⊕ κ → V := Sum.elim (fun i => Ψ (e i)) w
  have hu : ∀ i, Ψ (u i) = ∑ j, U i j • Ψ (e j) := fun i => by
    conv_lhs => rw [← e.sum_repr (u i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [U, e, map_sum, map_smul]
  have hfam : Sum.elim (Ψ ∘ u) w = fun a => ∑ b, M a b • y b := by
    funext a
    rcases a with i | k
    · simp [Fintype.sum_sum_type, M, y, hu]
    · simp [Fintype.sum_sum_type, M, y, Matrix.one_apply]
  have hGu : Matrix.gram ℝ u = U * U.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp [Matrix.gram_apply, U, PiLp.inner_apply, mul_comm]
  have hdet : (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det = U.det ^ 2 * (Matrix.gram ℝ y).det := by
    rw [hfam, GramContraction.gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one]
    ring
  have hP : ∏ i, ‖Ψ (e i)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => sq_nonneg _) fun i _ => by
      have := hΨ (e i); rw [e.orthonormal.1 i] at this
      nlinarith [norm_nonneg (Ψ (e i))]
  have hW : 0 ≤ ∏ j, ‖w j‖ ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hH := GramContraction.det_gram_le_prod y
  rw [Fintype.prod_sum_type] at hH
  rw [hdet, hGu, Matrix.det_mul, Matrix.det_transpose, ← sq]
  refine mul_le_mul_of_nonneg_left (hH.trans ?_) (sq_nonneg _)
  simpa [y] using mul_le_of_le_one_left hW hP

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChangeOfModel

variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]


open Classical in
def blockDeg (k₂ : K) : K → ℕ := fun k => if k = k₂ then 1 else 0


omit [Fintype K] [∀ k, Fintype (ι₂ k)] in
theorem isMultiHomog_linForm (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A q) (blockDeg q.1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  obtain ⟨k₀, j⟩ := q
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk]


omit [∀ k, Fintype (ι₂ k)] in
theorem exists_linForm_not_mem {P : Ideal (MRing ι)} {d : ℕ} {A : ∀ k, ι₂ k → ι k → ℤ} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A)) : ∀ k₂, ∃ j, ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  have := hprime
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end ChangeOfModel


open ChangeOfModel IndefiniteRowSideFullHecke.Inter in
theorem ChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometric.Statement) : ChangeOfModelStatement := by
  intro I hI K _ ι ι₂ _ _ P d A G J L L₁ hP hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K ι₂ P d (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm A) blockDeg hP
    (isMultiHomog_linForm A) (exists_linForm_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K))
  have e1 := hAI3 I hI K ι (K ⊕ K) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K ι₂ (K ⊕ K) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K) (Sum.elim ι ι₂) (I (K ⊕ K) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι ι₂ P d A (L₁ j) (L j) _ _ hP hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

open Module

theorem SublatticeExtension.linearIndependent_real_of_discrete {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ L) (hz : LinearIndependent ℤ v) :
    LinearIndependent ℝ v := by
  have hle : Submodule.span ℤ (Set.range v) ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 hv)
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (f := fun x => (⟨x.1, hle x.2⟩ : L))
      (continuous_subtype_val.subtype_mk _) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc]
  exact (finrank_span_eq_card hz).symm

theorem SublatticeExtension.proof : SublatticeExtension.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ ψ hφ hφ' hψ hnorm
  classical
  have mem : ∀ {G : Type} [AddCommGroup G] {n : ℕ} (χ : G →+ EuclideanSpace ℝ (Fin n)) (y),
      y ∈ imageLattice χ ↔ ∃ x, χ x = y := fun χ y => by
    rw [imageLattice, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddMonoidHom.mem_range]
  let b := Free.chooseBasis ℤ (imageLattice φ')
  let bR := b.ofZLatticeBasis ℝ (imageLattice φ')
  let g : _ → E' := fun i => Classical.choose ((mem φ' _).1 (b i).2)
  have hg : ∀ i, φ' (g i) = b i := fun i => Classical.choose_spec ((mem φ' _).1 (b i).2)
  let Ψ := bR.constr ℝ (fun i => φ (ψ (g i)))
  have hΨb : ∀ i, Ψ (b i) = φ (ψ (g i)) := fun i => by
    rw [← b.ofZLatticeBasis_apply ℝ (imageLattice φ') i]; exact bR.constr_basis ℝ _ i

  have hext : ∀ x, Ψ (φ' x) = φ (ψ x) := by
    intro x
    obtain ⟨c, hc⟩ : ∃ c : _ → ℤ, x = ∑ i, c i • g i := by
      refine ⟨b.repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩, hφ' ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp only [map_zsmul, hg]
      have hs := congrArg Subtype.val (b.sum_repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩)
      rw [Submodule.coe_sum] at hs; simp only [Submodule.coe_smul] at hs
      exact hs.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc]; simp only [map_sum, map_zsmul, hg, hΨb]

  have hlat : ∀ y ∈ imageLattice φ', ‖Ψ y‖ ≤ ‖y‖ := by
    intro y hy; obtain ⟨x, rfl⟩ := (mem φ' y).1 hy; rw [hext]; exact hnorm x
  let f : (_ → ℚ) → EuclideanSpace ℝ (Fin R') := fun q => bR.equivFun.symm (fun i => (q i : ℝ))
  have hf : DenseRange f :=
    (bR.equivFun.symm.surjective.denseRange).comp (DenseRange.piMap fun _ => Rat.denseRange_cast)
      (LinearMap.continuous_of_finiteDimensional bR.equivFun.symm.toLinearMap)
  have hrat : ∀ q, ‖Ψ (f q)‖ ≤ ‖f q‖ := by
    intro q
    have hNpos : (0 : ℝ) < (∏ i, (q i).den : ℕ) := by
      exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hz : ∀ i, ∃ z : ℤ, ((∏ i, (q i).den : ℕ) : ℝ) * (q i : ℝ) = z := by
      intro i
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
      refine ⟨k * (q i).num, ?_⟩
      have : ((∏ i, (q i).den : ℕ) : ℚ) * q i = k * (q i).num := by
        rw [hk]; push_cast; rw [mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      exact_mod_cast this
    choose z hz using hz
    have hmem : ((∏ i, (q i).den : ℕ) : ℝ) • f q ∈ imageLattice φ' := by
      have : ((∏ i, (q i).den : ℕ) : ℝ) • f q = ∑ i, z i • (b i : EuclideanSpace ℝ (Fin R')) := by
        simp only [f, Basis.equivFun_symm_apply, Finset.smul_sum, smul_smul, hz,
          ← Int.cast_smul_eq_zsmul ℝ, bR, Basis.ofZLatticeBasis_apply]
      rw [this]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
    have h := hlat _ hmem
    rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le] at h
    exact le_of_mul_le_mul_left h hNpos
  have hall : ∀ y, ‖Ψ y‖ ≤ ‖y‖ := by
    have hS : IsClosed {y | ‖Ψ y‖ ≤ ‖y‖} :=
      isClosed_le (continuous_norm.comp (LinearMap.continuous_of_finiteDimensional Ψ)) continuous_norm
    have hd : Dense {y | ‖Ψ y‖ ≤ ‖y‖} := Dense.mono (Set.range_subset_iff.2 fun q => hrat q) hf
    have h := hd.closure_eq
    rw [hS.closure_eq] at h
    exact Set.eq_univ_iff_forall.1 h

  have hvZ : LinearIndependent ℤ (fun i => φ (ψ (g i))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : ∑ i, c i • g i = 0 := by
      apply hψ; apply hφ; simpa [map_sum, map_zsmul] using hc
    have h1 : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      have := congrArg φ' h0
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_zsmul, hg] using this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h1
  have hvR := SublatticeExtension.linearIndependent_real_of_discrete (imageLattice φ) _
    (fun i => (mem φ _).2 ⟨ψ (g i), rfl⟩) hvZ
  refine ⟨Ψ, hext, hall, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hc := Fintype.linearIndependent_iff.1 hvR (bR.equivFun y)
    (by rw [← bR.constr_apply_fintype ℝ]; exact hy)
  exact bR.equivFun.injective (by ext i; simp [hc i])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockChainSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm Filter Asymptotics

noncomputable section

theorem TwoBlockChainSum.gridSum_chain (D i : ℕ) (hi : i ≤ D) :
    (fun n : ℕ => (∑ j ∈ Finset.range n,
        ((n - j - 1 : ℕ) : ℝ) ^ i * (j : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  refine (GridSum.proof D i hi).congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  have e1 : n - 1 - (n - j - 1) = j := by omega
  have e2 : n - 1 - j = n - j - 1 := by omega
  simp only [e1, e2]

theorem TwoBlockChainSum.gPoly_chain (D : ℕ) (c : ℕ → ℝ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n, gPoly D c (n - j - 1) j -
      (∑ i ∈ Finset.range (D + 1), c i) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
  refine (IsBigO.fun_sum fun i hi => (TwoBlockChainSum.gridSum_chain D i
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).const_mul_left (c i)).congr_left fun n => ?_
  unfold gPoly
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Finset.mul_sum]
  ring

theorem TwoBlockChainSum.proof (hL : TwoBlockStepLocal.Statement) (hB : TwoBlockStepBound.Statement) :
    TwoBlockChainSum.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨a₀, C, hC⟩ := hL D Ω κ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨K, hK⟩ := hB D Ω κ x B hX hx hBi hsp
  rw [← sum_twoBlockCoeff]
  generalize twoBlockCoeff I x (matAct B x) m m' D = c at hC ⊢
  generalize twoBlockStep x (matAct B x) = s at hC hK ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ i ∈ Finset.range (D + 1), |c i| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ Finset.sum_nonneg fun i _ => abs_nonneg _

  have hterm : ∀ n j : ℕ, j < n →
      |s (n - j - 1) j - gPoly D c (n - j - 1) j| ≤
        if a₀ ≤ n - j - 1 ∧ a₀ ≤ j then |C| * ((n : ℝ) ^ D / n) else (|K| + G) * (n : ℝ) ^ D := by
    intro n j hj
    have hn : ((n - j - 1 : ℕ) : ℝ) + (j : ℝ) + 1 = n := by
      have : n - j - 1 + j + 1 = n := by omega
      exact_mod_cast this
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    split_ifs with h
    · have h1 := hC (n - j - 1) j h.1 h.2
      rw [hn] at h1
      refine le_trans h1 ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    · have hg := abs_gPoly_le D c (n - j - 1) j
      have hn' : ((n - j - 1 + j : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_add]; exact hn
      rw [hn', ← hG] at hg
      have hk := hK (n - j - 1) j
      rw [hn] at hk
      have hk' : K * (n : ℝ) ^ D ≤ |K| * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self K) hpow
      calc _ ≤ |s (n - j - 1) j| + |gPoly D c (n - j - 1) j| := abs_sub _ _
        _ ≤ _ := by linarith

  have h1 : (fun n : ℕ => ∑ j ∈ Finset.range n, (s (n - j - 1) j - gPoly D c (n - j - 1) j)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.of_bound (|C| + 2 * a₀ * (|K| + G)) (Eventually.of_forall fun n => ?_)
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm n j (Finset.mem_range.mp hj)).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hgood : ((Finset.filter (fun j => a₀ ≤ n - j - 1 ∧ a₀ ≤ j) (Finset.range n)).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have hbad : ((Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card : ℝ) ≤ 2 * a₀ := by
      have hsub : Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n) ⊆
          Finset.range a₀ ∪ Finset.Ico (n - a₀) n := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_range, Nat.card_Ico] at hc
      have hc' : (Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card ≤ 2 * a₀ := by
        omega
      exact_mod_cast hc'
    have hcn : (n : ℝ) * ((n : ℝ) ^ D / n) ≤ (n : ℝ) ^ D := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.cast_zero, zero_mul]
        positivity
      · rw [mul_div_cancel₀]
        exact_mod_cast hn.ne'
    have hq : 0 ≤ (n : ℝ) ^ D / n := by positivity
    have hKG : 0 ≤ (|K| + G) * (n : ℝ) ^ D := mul_nonneg (add_nonneg (abs_nonneg K) hG0) hpow
    have e1 := mul_le_mul_of_nonneg_right hgood (mul_nonneg (abs_nonneg C) hq)
    have e2 := mul_le_mul_of_nonneg_right hbad hKG
    have e3 := mul_le_mul_of_nonneg_left hcn (abs_nonneg C)
    nlinarith
  refine (h1.add (TwoBlockChainSum.gPoly_chain D c)).congr_left fun n => ?_
  simp only [Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionAnyDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionAnyDegree

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionAnyDegree.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionAnyDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleiman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

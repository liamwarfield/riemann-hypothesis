module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarLoc

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CosetSumApply
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

def trm (Ht : G → ℝ≥0) (f : G → ℂ) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x

theorem lift_mR (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  unfold lift
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem resG_mR (F : G → ℂ) (g : G) (y : GR n) : resG ι F g (mR y) = F (g * ι y) := lift_mR _ _

theorem termSplit (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (z : ℂ) (x : G) :
    ∃ (y₀ : GR n) (C : ℂ), ∀ y : GR n, trm Ht f s₀ z (x * ι y) = C * fz m e (z - s₀) (mR (y₀ * y)) := by
  obtain ⟨x₀, y₀, S, r, hr, hx, hh⟩ := h.split x
  refine ⟨y₀, ((r : ℝ) : ℂ) ^ (z - s₀) * S, fun y => ?_⟩
  have hxy : x * ι y = x₀ * ι (y₀ * y) := by rw [hx, mul_assoc, ← map_mul]
  unfold trm
  rw [hxy, (hh _).1, (hh _).2, hS n m e (z - s₀) (y₀ * y), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (Vac.hLoc_nonneg _)]
  ring

theorem fz_mul_k (hS : SecFz) (w : ℂ) (y k : GR n) (hk : k ∈ KR n) :
    fz m e w (mR (y * k)) = fz m e w (mR y) * F0 m 0 e k := by
  obtain ⟨h1, h2⟩ := (mult n m 0 e).1 y k hk
  rw [hS n m e w (y * k), hS n m e w y, h1, h2]
  ring

theorem cosetSum_apply (Φ : G → ℂ) (x : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Φ x = ∑' q : GlobalTheory.Eis.Cosets Pp Γ, Φ (((q.out : Γ) : G) * x) := rfl

theorem klaw (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) :
    ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k := by
  intro z hz g y k hk
  have hfar : ∀ z' : ℂ, t < z'.re → Ê z' (g * ι (y * k)) = Ê z' (g * ι y) * F0 m 0 e k := by
    intro z' hz'
    rw [(h.far z' hz').2, (h.far z' hz').2, cosetSum_apply, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    obtain ⟨y₀, C, hC⟩ := termSplit hS h z' (((q.out : Γ) : G) * g)
    have e1 : ((q.out : Γ) : G) * (g * ι (y * k)) = ((q.out : Γ) : G) * g * ι (y * k) := by rw [mul_assoc]
    have e2 : ((q.out : Γ) : G) * (g * ι y) = ((q.out : Γ) : G) * g * ι y := by rw [mul_assoc]
    change trm Ht f s₀ z' _ = trm Ht f s₀ z' _ * _
    rw [e1, e2, hC, hC, ← mul_assoc y₀ y k, fz_mul_k hS _ _ _ hk]
    ring
  obtain ⟨σ, hσ⟩ := h.hR.1
  have hpre : IsPreconnected U := rightConn U h.hU h.hR
  have hA1 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι (y * k))) U := (h.hol _).analyticOnNhd h.hU
  have hA2 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι y) * F0 m 0 e k) U :=
    ((h.hol _).mul_const _).analyticOnNhd h.hU
  set z₀ : ℂ := ((max σ t + 1 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ U := hσ (by simp [z₀, GlobalTheory.Cont.rightOf]; linarith [le_max_left σ t])
  have hev : (fun z => Ê z (g * ι (y * k))) =ᶠ[𝓝 z₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
    have ho : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : z₀ ∈ {z : ℂ | t < z.re} := by simp [z₀]; linarith [le_max_right σ t]
    filter_upwards [ho.mem_nhds hm] with z hz using hfar z hz
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hpre hz₀ hev hz

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarIdOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopSeries
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IntegralTsumSupp
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsUnitOfInG
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem herm_herm (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [conjTranspose_apply, herm]
  apply Complex.ext <;> simp <;> ring

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_left_inverse (B := -(JJ n * xᴴ * JJ n))
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, hx, IwaPf.JJ_mul_self, neg_neg]

def grOf (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_grOf (x : M2 n) (hx : InG x) : mR (grOf x hx) = x := IsUnit.unit_spec _

def nG (s : Fin n → Fin n → ℝ) : GR n := grOf (nU (herm s)) (HolB.inG_upper (herm_herm s))

theorem mR_nG (s : Fin n → Fin n → ℝ) : mR (nG s) = nU (herm s) := IsUnit.unit_spec _

private theorem continuous_herm_cayley_coset_sums : Continuous (fun s : Fin n → Fin n → ℝ => herm s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [herm]
  fun_prop
private theorem continuous_nU_comp_herm :
    Continuous (fun s : Fin n → Fin n → ℝ => nU (herm s)) := by
  simp only [nU]
  exact Continuous.matrix_fromBlocks continuous_const continuous_herm_cayley_coset_sums continuous_const continuous_const

theorem continuous_nG : Continuous (nG (n := n)) := by
  show Continuous fun s => grOf (nU (herm s)) (HolB.inG_upper (herm_herm s))
  unfold grOf
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simpa only [Function.comp_def, IsUnit.unit_spec] using continuous_nU_comp_herm
  · have hinv : ∀ s : Fin n → Fin n → ℝ,
        ((isUnit_of_inG (HolB.inG_upper (herm_herm s))).unit⁻¹ : GL (Fin n ⊕ Fin n) ℂ).val =
          nU (-herm s) := by
      intro s
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      simp [nU, fromBlocks_multiply]
    have hc : Continuous (fun s : Fin n → Fin n → ℝ => nU (-herm s)) := by
      simp only [nU]
      exact Continuous.matrix_fromBlocks continuous_const continuous_herm_cayley_coset_sums.neg continuous_const
        continuous_const
    exact hc.congr fun s => (hinv s).symm

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem continuous_fzG (hS : SecFz) (w : ℂ) : Continuous fun Y : GR n => fz m e w (mR Y) := by
  have h1 : (fun Y : GR n => fz m e w (mR Y)) = fun Y => F0 m 0 e Y * ((hLoc Y : ℝ) : ℂ) ^ w :=
    funext fun Y => hS n m e w Y
  rw [h1]
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)) continuous_const fun Y => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (Vac.hLoc_pos detU1 Y)

theorem integral_tsum_supp {X : Type} [MeasurableSpace X] {ν : Measure X} {ι' : Type} (F : ι' → X → ℂ) (u : ι' → ℝ)
    (hu : Summable u) (hu0 : ∀ q, 0 ≤ u q) (bd : X → ℝ) (hbd : Integrable bd ν)
    (hF : ∀ q x, ‖F q x‖ ≤ u q * bd x) (hFm : ∀ q, AEStronglyMeasurable (F q) ν) :
    Summable (fun q => ∫ x, F q x ∂ν) ∧ ∫ x, ∑' q, F q x ∂ν = ∑' q, ∫ x, F q x ∂ν := by
  have hFi : ∀ q, Integrable (F q) ν := fun q =>
    Integrable.mono' (hbd.const_mul (u q)) (hFm q) (ae_of_all _ (hF q))
  have hIn : ∀ q, ‖∫ x, F q x ∂ν‖ ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ‖∫ x, F q x ∂ν‖ ≤ ∫ x, u q * bd x ∂ν := norm_integral_le_of_norm_le (hbd.const_mul (u q)) (ae_of_all _ (hF q))
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  refine ⟨Summable.of_norm_bounded (hu.mul_right _) hIn, ?_⟩
  have hF0 : ∀ q, q ∉ Function.support u → ∀ x, F q x = 0 := by
    intro q hq x
    have h0 : u q = 0 := Function.notMem_support.mp hq
    have := hF q x
    rw [h0, zero_mul] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL : ∀ x, ∑' q, F q x = ∑' s : Function.support u, F s x := by
    intro x
    refine (tsum_subtype_eq_of_support_subset (f := fun q => F q x) ?_).symm
    intro q hq
    by_contra h
    exact hq (hF0 q h x)
  have hN : ∀ q, ∫ x, ‖F q x‖ ∂ν ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ∫ x, ‖F q x‖ ∂ν ≤ ∫ x, u q * bd x ∂ν :=
          integral_mono (hFi q).norm (hbd.const_mul (u q)) (hF q)
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  have hsumn : Summable fun s : Function.support u => ∫ x, ‖F s x‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hN s)
      ((hu.subtype _).mul_right _)
  simp_rw [hL]
  rw [← integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) x => F s x) (fun s => hFi s) hsumn]
  refine tsum_subtype_eq_of_support_subset (f := fun q => ∫ x, F q x ∂ν) ?_
  intro q hq
  by_contra h
  exact hq (by simp only [hF0 q h, integral_zero])

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

private theorem isCompact_KR' (n : ℕ) : IsCompact ((KR n : Set (GR n))) := by
  classical
  let S : Set (M2 n) := {x | InG x ∧ xᴴ * x = 1}
  have hSc : IsClosed S := by
    change IsClosed ({x : M2 n | InG x} ∩ {x : M2 n | xᴴ * x = 1})
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq
        ((((continuous_id : Continuous (fun x : M2 n => x)).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (((continuous_id : Continuous (fun x : M2 n => x)).matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hBox : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hSsub : S ⊆ (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) := by
    intro x hx i _ j _
    have hu : x ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hx.2
    simpa using entry_norm_bound_of_unitary hu i j
  have hS : IsCompact S := hBox.of_isClosed_subset hSc hSsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let φ : S → GR n := fun x =>
    ⟨⟨x.1, x.1ᴴ, mul_eq_one_comm.mp x.2.2, x.2.2⟩, x.2.1⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    exact continuous_subtype_val.matrix_conjTranspose
  have hR : (KR n : Set (GR n)) = Set.range φ := by
    ext Y
    constructor
    · intro hY
      refine ⟨⟨mR Y, hY⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨x, rfl⟩
      exact x.2
  rw [hR]
  exact isCompact_range hφ

theorem topSeries (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) [MeasurableSpace (KR n)] [BorelSpace (KR n)]
    (μ : Measure (KR n)) [IsFiniteMeasure μ] {z : ℂ} (hz : t < z.re) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (hρ : Continuous ρ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (ha : InG a) (hb : InG b) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y))) ∧
    tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y) =
      d.eval z * ∑' q, C q * tOp μ (ιK n) ρ ψ a b (fz m e (z - s₀)) (mR (y₀ q * y)) := by
  classical
  haveI : CompactSpace (KR n) := isCompact_iff_compactSpace.mp (isCompact_KR' n)
  set A : GR n := grOf a ha with hA
  set B : GR n := grOf b hb with hB
  have hmul : ∀ Y₁ Y₂ : GR n, mR (Y₁ * Y₂) = mR Y₁ * mR Y₂ := fun _ _ => by simp [mR]
  have hY : ∀ (w : GR n) (k : KR n) (s : Fin n → Fin n → ℝ),
      mR w * ιK n k * a * nU (herm s) * b = mR (w * ((k : GR n) * A * nG s * B)) := by
    intro w k s
    simp only [hmul, ιK_apply, mR_nG, hA, hB, mR_grOf, mul_assoc]
  obtain ⟨hbd, hE⟩ := h.far z hz
  let P : KR n × (Fin n → Fin n → ℝ) → G := fun p => g * ι (y * ((p.1 : GR n) * A * nG p.2 * B))
  have hWc : Continuous fun p : KR n × (Fin n → Fin n → ℝ) => (p.1 : GR n) * A * nG p.2 * B :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_nG.comp continuous_snd)).mul continuous_const
  have hP : Continuous P := continuous_const.mul (h.ιc.comp (continuous_const.mul hWc))
  have hKc : IsCompact (P '' (Set.univ ×ˢ tsupport ψ)) := (isCompact_univ.prod hψc).image hP
  obtain ⟨u, hu, hub⟩ := hbd _ hKc
  have hterm : ∀ q (Y : GR n), GlobalTheory.Eis.term Pp Γ (fun x : G => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) (g * ι Y) q =
      C q * fz m e (z - s₀) (mR (y₀ q * Y)) := by
    intro q Y
    rw [← hyC q Y]
    simp only [GlobalTheory.Eis.term, trm, mul_assoc]
  have hBd : ∀ q (k : KR n) s, s ∈ tsupport ψ →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ |u q| := by
    intro q k s hs
    have h1 := hub (P (k, s)) ⟨(k, s), ⟨Set.mem_univ _, hs⟩, rfl⟩ q
    rw [hterm] at h1
    exact h1.trans (le_abs_self _)
  have hG : ∀ q, Continuous fun p : KR n × (Fin n → Fin n → ℝ) =>
      fz m e (z - s₀) (mR (y₀ q * (y * ((p.1 : GR n) * A * nG p.2 * B)))) := fun q =>
    (continuous_fzG (m := m) (e := e) hS (z - s₀)).comp (continuous_const.mul (continuous_const.mul hWc))
  have hfun : ∀ q (k : KR n) s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) =
      fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B)))) := by
    intro q k s
    rw [hY, mul_assoc]
  have hM : ∀ q, ∃ M : ℝ, ∀ (k : KR n) s, s ∈ tsupport ψ →
      ‖fz m e (z - s₀) (mR (y₀ q * (y * ((k : GR n) * A * nG s * B))))‖ ≤ M := by
    intro q
    obtain ⟨M, hM⟩ := (isCompact_univ.prod hψc).exists_bound_of_continuousOn (hG q).continuousOn
    exact ⟨M, fun k s hs => hM (k, s) ⟨Set.mem_univ _, hs⟩⟩
  have hψi : Integrable (fun s => ‖ψ s‖) := (hψ.integrable_of_hasCompactSupport hψc).norm
  have hzero : ∀ s, s ∉ tsupport ψ → ψ s = 0 := fun s hs => image_eq_zero_of_notMem_tsupport hs
  have hIc : ∀ q, Continuous fun k : KR n =>
      ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s := by
    intro q
    obtain ⟨M, hMb⟩ := hM q
    simp_rw [hfun]
    refine continuous_of_dominated (bound := fun s => M * ‖ψ s‖) ?_ ?_ (hψi.const_mul M) ?_
    · intro k
      exact (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ).aestronglyMeasurable
    · intro k
      refine Filter.Eventually.of_forall fun s => ?_
      by_cases hs : s ∈ tsupport ψ
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hMb k s hs) (norm_nonneg _)
      · simp [hzero s hs]
    · refine Filter.Eventually.of_forall fun s => ?_
      exact ((hG q).comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hv : Summable fun q => |u q| := hu.abs
  have hv0 : ∀ q, 0 ≤ |u q| := fun q => abs_nonneg _
  have hFb : ∀ q (k : KR n) s,
      ‖C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤ |u q| * ‖ψ s‖ := by
    intro q k s
    rw [hfun, ← mul_assoc, norm_mul]
    by_cases hs : s ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hBd q k s hs) (norm_nonneg _)
    · simp [hzero s hs]
  have hin : ∀ k : KR n,
      (Summable fun q => ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)) ∧
      ∫ s, ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) =
        ∑' q, ∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k
    refine integral_tsum_supp _ (fun q => |u q|) hv hv0 (fun s => ‖ψ s‖) hψi (fun q s => hFb q k s) ?_
    intro q
    simp_rw [hfun]
    exact (continuous_const.mul
      (((hG q).comp (continuous_const.prodMk continuous_id)).mul hψ)).aestronglyMeasurable
  have hIb : ∀ q (k : KR n),
      ‖C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by
    intro q k
    have h2 : ‖∫ s, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s)‖ ≤
        ∫ s, |u q| * ‖ψ s‖ :=
      norm_integral_le_of_norm_le (hψi.const_mul _) (Filter.Eventually.of_forall fun s => hFb q k s)
    rw [integral_const_mul] at h2
    rw [integral_const_mul] at h2
    rw [mul_left_comm, norm_mul, norm_mul]
    rw [norm_mul] at h2
    calc ‖ρ k‖ * (‖C q‖ * ‖∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s‖)
        ≤ ‖ρ k‖ * (|u q| * ∫ s, ‖ψ s‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = |u q| * (‖ρ k‖ * ∫ s, ‖ψ s‖) := by ring
  have hbdρ : Integrable (fun k : KR n => ‖ρ k‖ * ∫ s, ‖ψ s‖) μ :=
    (hρ.norm.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hout := integral_tsum_supp (ν := μ)
    (fun q k => C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s))
    (fun q => |u q|) hv hv0 _ hbdρ hIb
    (fun q => (continuous_const.mul (hρ.mul (hIc q))).aestronglyMeasurable)
  have hpt : ∀ (k : KR n) s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
      d.eval z * ∑' q, C q * (fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
    intro k s
    rw [hY, resG_mR, hE, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfun, ← mul_assoc (C q), ← hyC q]
    simp only [trm, mul_assoc]
  refine ⟨?_, ?_⟩
  · refine hout.1.congr fun q => ?_
    simp only [tOp, integral_const_mul]
  · have hL : ∀ k : KR n, ρ k * ∫ s, resG ι (Ê z) g (mR y * ιK n k * a * nU (herm s) * b) * ψ s =
        d.eval z * ∑' q, C q * (ρ k * ∫ s, fz m e (z - s₀) (mR (y₀ q * y) * ιK n k * a * nU (herm s) * b) * ψ s) := by
      intro k
      simp_rw [hpt k]
      rw [integral_const_mul, (hin k).2]
      simp_rw [integral_const_mul]
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      refine tsum_congr fun q => ?_
      ring
    simp only [tOp]
    simp_rw [hL]
    rw [integral_const_mul, hout.2]
    congr 1
    refine tsum_congr fun q => ?_
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DirSeries
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem dirSeries (hC : CurveGR) (hF : FzDer) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) {z : ℂ} (hz : t < z.re)
    (Z : M2 n) (b : Bool) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0) ∧
    deriv (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 =
      d.eval z * ∑' q, C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 := by
  obtain ⟨γ, hγc, hγ0, hγadd, hγe⟩ := hC n Z b
  obtain ⟨Cd, hCd0, hR⟩ := hF n m e (z - s₀) Z b
  choose Rf hRf using hR
  have hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
      fz m e (z - s₀) (mR (y₁ * γ s)) := by
    intro y₁ s
    rw [mR_mul, hγe]
  have hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s := by
    intro y₁ s
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)
    have hfe : (fun u : ℝ => fz m e (z - s₀)
        (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) =
        fun x : ℝ => fz m e (z - s₀)
          (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))) := by
      funext u
      rw [hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]
    rw [hfe]
    exact h1
  have hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))
  obtain ⟨u, hu, hbound⟩ := (h.far z hz).1 _ hK
  have hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q := by
    intro q s hs
    have hb := hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q
    rw [mul_assoc (y₀ q), ← hyC q (y * γ s)]
    simpa only [GlobalTheory.Eis.term, trm, mul_assoc] using hb
  have hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q := by
    intro q s hs
    have h1 := (hRf (y₀ q * y * γ s)).2
    have h2 := hterm q s (Ioo_subset_Icc_self hs)
    rw [norm_mul] at h2 ⊢
    calc ‖C q‖ * ‖Rf (y₀ q * y * γ s)‖
        ≤ ‖C q‖ * (Cd * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cd * (‖C q‖ * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) := by ring
      _ ≤ Cd * u q := mul_le_mul_of_nonneg_left h2 hCd0
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun q => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))) :=
    hu.of_norm_bounded fun q => by
      simpa only [hfzγ] using hterm q 0 ⟨by norm_num, by norm_num⟩
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo
    (g := fun q (s : ℝ) => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))))
    (g' := fun q s => C q * Rf (y₀ q * y * γ s))
    (fun q s _ => (hderiv (y₀ q * y) s).const_mul (C q)) hbd h0mem hg0 h0mem
  rw [hγ0] at hsum
  simp only [mul_one] at hsum
  have hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y) :=
    fun q => (hRf (y₀ q * y)).1.deriv
  have hfun : (fun s : ℝ => resG ι (Ê z) g
      (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) =
      fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) := by
    funext s
    have hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
        Ê z (g * ι (y * γ s)) := by
      rw [← hγe, ← mR_mul, resG_mR]
    rw [hl, (h.far z hz).2]
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]
  simp only [hRfd]
  refine ⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩
  · simpa only [hγ0, mul_one] using hbd q 0 h0mem
  · rw [hfun, (hsum.const_mul (d.eval z)).deriv]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FarP

theorem farId_of (hC : CurveGR) (hF : FzDer) : FarId := by
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD hS _ _ μ _ _ Q N ρ ψ a b D M hρ hψ hab hDd hM hid
  refine ⟨⟨t, ?_⟩, FarP.klaw hS hD⟩
  intro z hz g y
  have key : ∀ (F : M2 n → ℂ) (x : M2 n), rC (lowQ Q) F x =
      deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    intro F x
    simp only [rC, dir1, dir2, if_true]
    rfl
  choose y₀ C hyC using fun q : GlobalTheory.Eis.Cosets Pp Γ => FarP.termSplit hS hD z (↑(Quotient.out q) * g)
  have d1 := FarP.dirSeries hC hF hD hz (lowQ Q) true g y y₀ C hyC
  have d2 := FarP.dirSeries hC hF hD hz (lowQ Q) false g y y₀ C hyC
  have tp := fun l : Fin N => FarP.topSeries hS hD μ hz (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1
    (hab l).1 (hab l).2 g y y₀ C hyC
  have hq : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) =
      ∑ l : Fin N, M l (z - s₀) * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    intro q
    have h := hid (z - s₀) (mR (y₀ q * y)) (y₀ q * y).2
    rw [key] at h
    exact h
  rw [key, d1.2, d2.2, Finset.sum_congr rfl (fun l _ => by rw [(tp l).2])]
  have e1 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (d1.1.mul_left _).tsum_add (d2.1.mul_left _)]
    congr 1
    funext q
    ring
  have e2 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      ∑ l : Fin N, M l (z - s₀) * ∑' q, C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    have hq2 : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
        ∑ l : Fin N, M l (z - s₀) * (C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y))) := by
      intro q
      rw [hq q, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [tsum_congr hq2]
    rw [Summable.tsum_finsetSum (fun l _ => ((tp l).1.mul_left (M l (z - s₀))))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← tsum_mul_left]
  have e3 := e1.symm.trans e2
  calc D (z - s₀) * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0))
        = Polynomial.eval z d * (D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) := by ring
    _ = _ := by
      rw [e3, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzDer
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ReConjMulLe
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveHasDerivAt
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem cd_det_lemma {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have he : ∀ i j : ι, ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x i j) := fun i j =>
    contDiff_apply_apply ℂ i j
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => he _ _)))

theorem cd_det : ContDiff ℂ ∞ (fun x : M2 n => x.det) := by
  exact cd_det_lemma

theorem cd_detu1 : ContDiff ℂ ∞ (fun x : M2 n => (u1 x).det) := by
  exact cd_det_lemma.comp contDiff_first_cayley_block

theorem curve_hasDerivAt (X x : M2 n) : HasDerivAt (fun s : ℝ => x * cE X s) (x * X) 0 := by
  have h := (mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cE_hasDerivAt0 X)
  simp only [Function.comp_def, mulL_apply] at h
  exact h

theorem curve_deriv (Ψ : M2 n → ℂ) (hΨ : ContDiff ℂ ∞ Ψ) (X x : M2 n) :
    HasDerivAt (fun s : ℝ => Ψ (x * cE X s)) (fderiv ℂ Ψ x (x * X)) 0 := by
  have hd : HasFDerivAt Ψ (fderiv ℂ Ψ x) (x * cE X 0) := by
    rw [cE_zero, Matrix.mul_one]
    exact (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt X x)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h
  exact h

theorem continuous_mR' : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem det_mR_ne' (g : GR n) : (mR g).det ≠ 0 := by
  show ((g : GL (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n ⊕ Fin n) ℂ).isUnit).ne_zero

def rD (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => x.det) x (x * X) / x.det

def rA (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => (u1 x).det) x (x * X) / (u1 x).det

private theorem rD_mul_left_eq_of_det_ne_zero (P A X : M2 n) (hP : P.det ≠ 0) : rD X (P * A) = rD X A := by
  unfold rD
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => x.det) (fderiv ℂ (fun x : M2 n => x.det) B) B :=
    fun B => ((cd_det (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (P * y).det)
      ((fderiv ℂ (fun x : M2 n => x.det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (P * y).det)
      (P.det • fderiv ℂ (fun x : M2 n => x.det) A) A := by
    simp_rw [Matrix.det_mul]
    exact (hdet A).const_mul P.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, Matrix.det_mul, mul_div_mul_left _ _ hP]

theorem rD_up (X : M2 n) (p k : GR n) : rD X (mR p * mR k) = rD X (mR k) := by
  exact rD_mul_left_eq_of_det_ne_zero _ _ X (det_mR_ne' p)

private theorem rA_mul_left_eq_of_u1_mul (D : Matrix (Fin n) (Fin n) ℂ) (P A X : M2 n) (hD : D.det ≠ 0)
    (hu : ∀ y, u1 (P * y) = D * u1 y) : rA X (P * A) = rA X A := by
  unfold rA
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => (u1 x).det) (fderiv ℂ (fun x : M2 n => (u1 x).det) B) B :=
    fun B => ((cd_detu1 (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      ((fderiv ℂ (fun x : M2 n => (u1 x).det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      (D.det • fderiv ℂ (fun x : M2 n => (u1 x).det) A) A := by
    simp_rw [hu, Matrix.det_mul]
    exact (hdet A).const_mul D.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, hu, Matrix.det_mul, mul_div_mul_left _ _ hD]

theorem rA_up (X : M2 n) (p k : GR n) (hp : IsUp p) : rA X (mR p * mR k) = rA X (mR k) := by
  have hD : (toBlocks₂₂ (mR p)).det ≠ 0 := by
    rw [← first_block_of_upper p hp]
    exact det_first_cayley_block_ne_zero p.2
  exact rA_mul_left_eq_of_u1_mul _ _ _ X hD (fun y => first_block_upper_mul p y hp)

theorem continuous_rD (X : M2 n) : Continuous fun k : GR n => rD X (mR k) := by
  unfold rD
  refine Continuous.div ?_ (cd_det.continuous.comp continuous_mR') (fun k => det_mR_ne' k)
  exact ((cd_det.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

theorem continuous_rA (X : M2 n) : Continuous fun k : GR n => rA X (mR k) := by
  unfold rA
  refine Continuous.div ?_ (cd_detu1.continuous.comp continuous_mR')
    (fun k => (det_u_ne (x := mR k) k.2).1)
  exact ((cd_detu1.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

end PositivityTheory.Rg.Sw.HSt.FL
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_curve {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) (s : ℝ) :
    fz m e w (x * cE X s) = (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) := by
  have hg : InG (x * cE X s) := inG_mul hx (inG_cE hX s)
  have hd := det_first_cayley_block_ne_zero hg
  have hmul : (u1 (x * cE X s)).det * (ub1 (x * cE X s)).det =
      ((Complex.normSq (u1 (x * cE X s)).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_adjoint hg, Matrix.det_conjTranspose]
    exact Complex.mul_conj _
  have hpos : (0 : ℝ) < Complex.normSq (u1 (x * cE X s)).det := Complex.normSq_pos.mpr hd
  unfold fz
  rw [hmul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), Complex.ofReal_log hpos.le]

theorem fz_deriv {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) :
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (x * cE X s)) R 0 ∧
      ‖R‖ ≤ ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
  have hd0 : det x ≠ 0 := (isUnit_det_of_InG hx).ne_zero
  have ha0 : (u1 x).det ≠ 0 := det_first_cayley_block_ne_zero hx
  have hfun : (fun s : ℝ => fz m e w (x * cE X s)) = fun s : ℝ =>
      (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
        Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) :=
    funext fun s => fz_curve hX hx m e w s
  have hf0 : fz m e w x = (det x) ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w)) := by
    have h := fz_curve hX hx m e w 0
    rw [cE_zero, mul_one] at h
    exact h
  have hD : HasDerivAt (fun s : ℝ => det (x * cE X s))
      ((fderiv ℂ (fun y : M2 n => det y) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => det y) cd_det X x
  have hA : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => (u1 y).det) cd_detu1 X x
  have hD0 : det (x * cE X 0) = det x := by rw [cE_zero, mul_one]
  have hA0 : (u1 (x * cE X 0)).det = (u1 x).det := by rw [cE_zero, mul_one]
  have hzD : HasDerivAt (fun z : ℂ => z ^ e) (↑e * det x ^ (e - 1)) (det (x * cE X 0)) := by
    rw [hD0]
    exact hasDerivAt_zpow e (det x) (Or.inl hd0)
  have hzA : HasDerivAt (fun z : ℂ => z ^ (-(m : ℤ)))
      (↑(-(m : ℤ)) * (u1 x).det ^ (-(m : ℤ) - 1)) ((u1 (x * cE X 0)).det) := by
    rw [hA0]
    exact hasDerivAt_zpow _ _ (Or.inl ha0)
  have hDz := hzD.comp (0 : ℝ) hD
  have hAz := hzA.comp (0 : ℝ) hA
  have hre : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.re)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).re 0 := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have him : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.im)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).im 0 := by
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have hN := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => Complex.normSq_apply (u1 (x * cE X s)).det)
  have hNne : Complex.normSq (u1 (x * cE X 0)).det ≠ 0 := by
    rw [hA0]
    exact (Complex.normSq_pos.mpr ha0).ne'
  have hL := hN.log hNne
  have hE := (hL.ofReal_comp.mul_const (-w)).cexp
  have hfin := (hDz.mul hAz).mul hE
  rw [hfun]
  refine ⟨_, hfin, ?_⟩
  simp only [hA0, hD0, Function.comp_apply]
  have hd' : (fderiv ℂ (fun y : M2 n => det y) x) (x * X) = rD X x * det x := by
    unfold rD
    field_simp
  have ha' : (fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X) = rA X x * (u1 x).det := by
    unfold rA
    field_simp
  have bound : ‖(det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w))) *
      ((e : ℂ) * rD X x + (-(m : ℂ)) * rA X x + ((2 * (rA X x).re : ℝ) : ℂ) * (-w))‖ ≤
      ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
    rw [norm_mul, hf0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine norm_add₃_le.trans ?_
    have h1 : |(rA X x).re| ≤ ‖rA X x‖ := Complex.abs_re_le_norm _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    simp only [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  convert bound using 2
  rw [hd', ha']
  have hq : ((rA X x * (u1 x).det).re * (u1 x).det.re + (u1 x).det.re * (rA X x * (u1 x).det).re +
      ((rA X x * (u1 x).det).im * (u1 x).det.im + (u1 x).det.im * (rA X x * (u1 x).det).im)) /
      Complex.normSq (u1 x).det = 2 * (rA X x).re := by
    have hn : Complex.normSq (u1 x).det ≠ 0 := (Complex.normSq_pos.mpr ha0).ne'
    rw [div_eq_iff hn, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [hq]
  simp only [Pi.mul_apply, Function.comp_apply, cE_zero, mul_one]
  rw [zpow_sub_one₀ hd0, zpow_sub_one₀ ha0]
  push_cast
  field_simp

end PositivityTheory.Rg.Sw.HSt.FL
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FL
open PositivityTheory.Rg.Sw.LVs.II (cE)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fzDer : FzDer := by
  intro n m e w Z b
  have hX : IsLie (if b = true then dir1 Z else dir2 Z) := lie_dir Z b
  haveI := kRCpt n
  have hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rD _).comp continuous_subtype_val
  have hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rA _).comp continuous_subtype_val
  obtain ⟨C1, hC1⟩ := (isCompact_range hc1).isBounded.exists_norm_le
  obtain ⟨C2, hC2⟩ := (isCompact_range hc2).isBounded.exists_norm_le
  refine ⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  obtain ⟨R, hR, hRb⟩ := fz_deriv (x := mR (p * k)) hX (p * k).2 m e w
  refine ⟨R, ?_, ?_⟩
  · simp only [cE_eq_exp]
    exact hR
  · refine hRb.trans ?_
    have e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rD (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rD_up]
    have e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rA (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rA_up _ _ _ hp]
    have b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0 :=
      (hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    have b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0 :=
      (hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    rw [e1, e2, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    gcongr

end PositivityTheory.Rg.Sw.HSt
end
end

namespace PositivityTheory.Rg.Sw.HSt

theorem farId : FarId := farId_of curveGR fzDer

end PositivityTheory.Rg.Sw.HSt

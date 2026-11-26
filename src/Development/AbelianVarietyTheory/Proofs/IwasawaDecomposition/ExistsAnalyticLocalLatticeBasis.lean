module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisOfClosedBall
set_option autoImplicit false

namespace GlobalTheory.LatticeBasisClosedBall

theorem exists_real_coords {g : ℕ} (lam : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (w : Fin g → ℂ) : ∃ c : Fin (2 * g) → ℝ, ∑ j, c j • lam j = w := by
  have hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hspan : Submodule.span ℝ (Set.range lam) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hdim
  have hw : w ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw

theorem isLatBasis_of_closedBall : ∀ {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ)
    (R : ℝ), LinearIndependent ℝ lam → (∀ j : Fin (2 * g), lam j ∈ H) → ∑ j : Fin (2 * g), ‖lam j‖ ≤ R →
    (∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H →
      ∃ m : Fin (2 * g) → ℤ, w = ∑ j : Fin (2 * g), m j • lam j) →
    GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (↑H : Set (Fin g → ℂ)) lam := by
  intro g H lam R hli hmem hR hball
  have hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H := fun m =>
    H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)
  refine ⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_real_coords lam hli w
    have hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    have hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H := H.sub_mem hw (hint _)
    have hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R := by
      rw [mem_closedBall_zero_iff, hsplit]
      refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    obtain ⟨m, hm⟩ := hball _ hnorm hH
    refine ⟨fun j => m j + ⌊c j⌋, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hm, sub_add_cancel]
  · rintro ⟨m, rfl⟩
    exact hint m

end GlobalTheory.LatticeBasisClosedBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.eventually_mem_of_graph {n g : ℕ} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} {b₀ : Fin n → ℂ}
    {w₀ : Fin g → ℂ} {ζ : (Fin n → ℂ) → Fin g → ℂ} (hζ0 : ζ b₀ = w₀) (hζc : ContinuousAt ζ b₀)
    (hζ : ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1) : ∀ᶠ b in 𝓝 b₀, ζ b ∈ K b := by
  have ht : Filter.Tendsto (fun b => (b, ζ b)) (𝓝 b₀) (𝓝 (b₀, w₀)) := by
    have := (continuousAt_id.prodMk hζc).tendsto
    simpa [hζ0] using this
  filter_upwards [ht.eventually hζ] with b hb
  exact hb.2 rfl

theorem exists_isLatBasis_of_discrete {g : ℕ} (H : AddSubgroup (Fin g → ℂ))
    (hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H → w = 0)
    (hs : Submodule.span ℝ (H : Set (Fin g → ℂ)) = ⊤) :
    ∃ β : Fin (2 * g) → Fin g → ℂ, IsLatBasis (H : Set (Fin g → ℂ)) β := by
  set L : Submodule ℤ (Fin g → ℂ) := H.toIntSubmodule with hL
  have hLset : (L : Set (Fin g → ℂ)) = H := rfl
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hd
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext (hU x.1 hx x.2)
    · rintro rfl
      exact h0U
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hs⟩
  have hr : Module.finrank ℤ L = 2 * g := by
    rw [ZLattice.rank ℝ L, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨fun j => (b j : Fin g → ℂ), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have he : (fun j => (b j : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ L) :=
      funext fun j => (Module.Basis.ofZLatticeBasis_apply ℝ L b j).symm
    rw [he]
    exact (b.ofZLatticeBasis ℝ L).linearIndependent
  · refine ⟨b.repr ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun x : L => (x : Fin g → ℂ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · rintro ⟨m, rfl⟩
    exact H.sum_mem fun j _ => H.zsmul_mem (b j).2 _

theorem IsLatFam.eventually_intComb {n g r : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    {b₀ : Fin n → ℂ} (hK : IsLatFam B K) (hb₀ : b₀ ∈ B) {lam : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (hlc : ContinuousAt lam b₀) (hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, lam b j ∈ K b) (hβ : IsLatBasis (K b₀) (lam b₀))
    (y : Fin g → ℂ) :
    ∀ᶠ q in 𝓝 (b₀, y), q.2 ∈ K q.1 → ∃ m : Fin r → ℤ, q.2 = ∑ j, m j • lam q.1 j := by
  by_cases hy : y ∈ K b₀
  · obtain ⟨m, hm⟩ := (hβ.2 y).1 hy
    obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ y hy
    set f : (Fin n → ℂ) → Fin g → ℂ := fun b => ∑ j, m j • lam b j with hf
    have hfc : ContinuousAt f b₀ := by
      have : Continuous (fun v : Fin r → Fin g → ℂ => ∑ j, m j • v j) := by fun_prop
      exact this.continuousAt.comp hlc
    have hf0 : f b₀ = y := hm.symm
    have hfK : ∀ᶠ b in 𝓝 b₀, f b ∈ K b := by
      filter_upwards [hlK, hK.1.mem_nhds hb₀] with b hb hbB
      obtain ⟨H, hH⟩ := hK.2.1 b hbB
      rw [← hH] at hb ⊢
      exact H.sum_mem fun j _ => H.zsmul_mem (hb j) _
    have ht : Filter.Tendsto (fun b => (b, f b)) (𝓝 b₀) (𝓝 (b₀, y)) := by
      have := (continuousAt_id.prodMk hfc).tendsto
      simpa [hf0] using this
    have hfζ : ∀ᶠ b in 𝓝 b₀, f b = ζ b := by
      filter_upwards [ht.eventually hζ, hfK] with b h1 h2
      exact h1.1 h2
    have hq : ∀ᶠ q : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, y), f q.1 = ζ q.1 :=
      (continuous_fst.tendsto (b₀, y)).eventually hfζ
    filter_upwards [hq, hζ] with q h1 h2 h3
    exact ⟨m, (h2.1 h3).trans h1.symm⟩
  · have ho := hK.2.2.1.mem_nhds (show (b₀, y) ∈ {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} from ⟨hb₀, hy⟩)
    filter_upwards [ho] with q hq h
    exact absurd h hq.2

theorem isLatBasis_of_ball {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ) (R : ℝ)
    (hli : LinearIndependent ℝ lam) (hmem : ∀ j, lam j ∈ H) (hR : ∑ j, ‖lam j‖ ≤ R)
    (hball : ∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • lam j) :
    IsLatBasis (H : Set (Fin g → ℂ)) lam := by
  first
  | exact @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | (apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall ..)

theorem IsLatFam.exists_analytic_locBasis : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    ∃ lam : (Fin n → ℂ) → Fin (2 * g) → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b) := by
  intro n g B K b₀ hK hb₀ hs
  obtain ⟨H₀, hH₀⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH₀]; exact H₀.zero_mem
  obtain ⟨ζ₀, hζ₀0, -, hζ₀⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H₀ → w = 0 := by
    have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    filter_upwards [ht.eventually hζ₀] with w hw hwH
    have hwK : w ∈ K b₀ := by rw [← hH₀]; exact hwH
    rw [hw.1 hwK, hζ₀0]
  obtain ⟨β, hβ⟩ := exists_isLatBasis_of_discrete H₀ hd (by rw [hH₀]; exact hs)
  rw [hH₀] at hβ
  have hβK : ∀ j, β j ∈ K b₀ := fun j =>
    (hβ.2 (β j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  choose ζ hζ0 hζa hζ using fun j => hK.2.2.2 b₀ hb₀ (β j) (hβK j)
  have hla : AnalyticAt ℂ (fun b j => ζ j b) b₀ := AnalyticAt.pi hζa
  have hlc := hla.continuousAt
  have hl0 : (fun j => ζ j b₀) = β := funext hζ0
  have hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, ζ j b ∈ K b :=
    Filter.eventually_all.2 fun j => IsLatFam.eventually_mem_of_graph (hζ0 j) (hζa j).continuousAt (hζ j)
  have hβ' : IsLatBasis (K b₀) ((fun b j => ζ j b) b₀) := by
    show IsLatBasis (K b₀) (fun j => ζ j b₀)
    rw [hl0]; exact hβ
  set R : ℝ := ∑ j, (‖β j‖ + 1) with hR
  have hball := (isCompact_closedBall (0 : Fin g → ℂ) R).eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b w => w ∈ K b → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • ζ j b) fun y _ => IsLatFam.eventually_intComb hK hb₀ hlc hlK hβ' y
  have hli : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ (fun j => ζ j b) := by
    have h1 : LinearIndependent ℝ ((fun b j => ζ j b) b₀) := hβ'.1
    exact hlc.tendsto.eventually h1.eventually
  have hnorm : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖ζ j b‖ ≤ ‖β j‖ + 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => ‖ζ j b‖) b₀ := (hζa j).continuousAt.norm
    have hlt : (fun b => ‖ζ j b‖) b₀ < (fun _ => ‖β j‖ + 1) b₀ := by simp [hζ0 j]
    filter_upwards [hc.eventually_lt continuousAt_const hlt] with b hb
    exact hb.le
  refine ⟨fun b j => ζ j b, hla, ?_⟩
  filter_upwards [hball, hli, hnorm, hlK, hK.1.mem_nhds hb₀] with b h1 h2 h3 h4 h5
  obtain ⟨H, hH⟩ := hK.2.1 b h5
  rw [← hH]
  refine isLatBasis_of_ball H _ R h2 (fun j => ?_) (Finset.sum_le_sum fun j _ => h3 j) fun w hw hwH => ?_
  · show ζ j b ∈ (H : Set (Fin g → ℂ)); rw [hH]; exact h4 j
  · exact h1 w hw (by rw [← hH]; exact hwH)

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_local_lattice_basis : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → ∃ lam : (Fin n → ℂ) → Fin (2 * g) → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.IsLatFam.exists_analytic_locBasis | exact GlobalTheory.ShFam.Hor.LogCh.IsLatFam.exists_analytic_locBasis | (intros; apply GlobalTheory.ShFam.Hor.LogCh.IsLatFam.exists_analytic_locBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoisoCount

open Matrix

theorem vecMul_eq_zero_of_rows_li {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : LinearIndependent K (fun i => X i)) (y : m → K)
    (hy : y ᵥ* X = 0) : y = 0 := by
  rw [Fintype.linearIndependent_iff] at h
  funext i; exact h y (by rw [← vecMul_eq_sum]; exact hy) i

theorem rows_li_of_vecMul {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) :
    LinearIndependent K (fun i => X i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [h g (by rw [vecMul_eq_sum]; exact hg)]; rfl

theorem det_gram_ne_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] (X : Matrix m n K)
    (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) : (X * Xᵀ).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hd
  apply hy0; apply h
  apply dotProduct_self_eq_zero.1
  have : (y ᵥ* X) ⬝ᵥ (y ᵥ* X) = y ⬝ᵥ (X *ᵥ (y ᵥ* X)) := by rw [dotProduct_mulVec]
  rw [this, ← vecMul_transpose, vecMul_vecMul, hy, dotProduct_zero]

theorem gram_map {K : Type*} [CommRing K] {m n : Type*} [Fintype n] (Z : Matrix m n ℤ) :
    Z.map (Int.cast : ℤ → K) * (Z.map (Int.cast : ℤ → K))ᵀ = (Z * Zᵀ).map (Int.cast : ℤ → K) := by
  ext i j; simp [Matrix.mul_apply]

theorem det_map_intCast {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) : (Z.map (Int.cast : ℤ → K)).det = (Z.det : K) := by
  have := RingHom.map_det (Int.castRingHom K) Z
  simpa using this.symm

theorem rank_bound {r r₀ : ℕ} (P : Matrix (Fin r₀) (Fin r₀) ℤ)
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ x ∈ S, P.map (Int.cast : ℤ → ZMod N) *ᵥ x = 0) :
    r + (P.map (Int.cast : ℤ → ℝ)).rank ≤ 2 * r₀ := by
  classical
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' ℝ (fun k => Pr k)
  haveI : Finite κ := Finite.of_injective c hc
  letI : Fintype κ := Fintype.ofFinite κ
  have hρ : Pr.rank = Nat.card κ := by
    rw [Matrix.rank_eq_finrank_span_row, Nat.card_eq_fintype_card, ← finrank_span_eq_card hli, hsp]; rfl
  set R : Matrix κ (Fin r₀) ℤ := P.submatrix c id with hR
  have hRr : ∀ y : κ → ℝ, y ᵥ* R.map (Int.cast : ℤ → ℝ) = 0 → y = 0 :=
    vecMul_eq_zero_of_rows_li _ hli
  have hd0 : (R * Rᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero _ hRr
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  set d := (R * Rᵀ).det
  set N := d.natAbs + 1 with hN
  have hN2 : 2 ≤ N := by have := Int.natAbs_pos.2 hd0; omega
  haveI : NeZero N := ⟨by omega⟩
  have hu : IsUnit (d : ZMod N) := by
    have h1 : ((d.natAbs : ℕ) : ZMod N) = -1 := by
      have : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
      rw [hN] at this; push_cast at this; exact eq_neg_of_add_eq_zero_left this
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast, h1]; exact isUnit_one.neg
    · rw [h, Int.cast_neg, Int.cast_natCast, h1, neg_neg]; exact isUnit_one
  obtain ⟨S, hcard, hSk⟩ := hS N (by omega)
  set RN := R.map (Int.cast : ℤ → ZMod N) with hRN
  let f : (Fin r₀ → ZMod N) →+ (κ → ZMod N) := RN.mulVecLin.toAddMonoidHom
  have hsurj : Function.Surjective f := by
    intro z
    have hG : IsUnit (RN * RNᵀ).det := by rw [hRN, gram_map, det_map_intCast]; exact hu
    refine ⟨RNᵀ *ᵥ ((RN * RNᵀ)⁻¹ *ᵥ z), ?_⟩
    show RN *ᵥ (RNᵀ *ᵥ _) = z
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, one_mulVec]
  have hkc : Nat.card f.ker * N ^ Nat.card κ = N ^ r₀ := by
    have h1 := f.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
      Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r₀),
      Fintype.card_fin] at h1
    exact h1
  have hsub : S ⊆ (f.ker : Set (Fin r₀ → ZMod N)) := by
    intro x hx
    show RN *ᵥ x = 0
    funext k
    have := congrFun (hSk x hx) (c k)
    exact this
  have hle : Nat.card S ≤ Nat.card f.ker := Nat.card_mono (Set.toFinite _) hsub
  have key : N ^ r * N ^ Nat.card κ ≤ N ^ r₀ * N ^ r₀ := by
    rw [← hcard, ← hkc, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hle)
  rw [← pow_add, ← pow_add] at key
  have := (Nat.pow_le_pow_iff_right hN2).1 key
  rw [hρ]; omega

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem ker_le_span {r r₀ : ℕ} (Mr : Matrix (Fin r) (Fin r) ℝ) (Ar : Matrix (Fin r₀) (Fin r) ℝ)
    (hM : IsUnit Mr.det) (hA : LinearIndependent ℝ (fun i => Ar i))
    (hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀) :
    LinearMap.ker (Ar * Mrᵀ).mulVecLin ≤ Submodule.span ℝ (Set.range fun i => Ar i) := by
  set T := (Ar * Mrᵀ).mulVecLin
  set E := Arᵀ.mulVecLin
  have hE : Function.Injective E := by
    intro x y hxy
    have : (x - y) ᵥ* Ar = 0 := by
      rw [sub_vecMul, ← mulVec_transpose, ← mulVec_transpose]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (vecMul_eq_zero_of_rows_li _ hA _ this)
  have hrE : LinearMap.range E = Submodule.span ℝ (Set.range fun i => Ar i) := by
    rw [Matrix.range_mulVecLin]; rfl
  have hAr : Ar.rank = r₀ := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => Ar i)) = r₀
    rw [finrank_span_eq_card hA, Fintype.card_fin]
  have hT : Module.finrank ℝ (LinearMap.range T) = r₀ := by
    change (Ar * Mrᵀ).rank = r₀
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]), hAr]
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ E)
  have hQ : Module.finrank ℝ (LinearMap.range (T ∘ₗ E)) = (Ar * Mrᵀ * Arᵀ).rank := by
    rw [Matrix.rank, Matrix.mulVecLin_mul]
  have hmap : Submodule.map E (LinearMap.ker (T ∘ₗ E)) = LinearMap.range E ⊓ LinearMap.ker T := by
    rw [LinearMap.ker_comp, Submodule.map_comap_eq]
  have h3 : Module.finrank ℝ (LinearMap.range E ⊓ LinearMap.ker T : Submodule ℝ (Fin r → ℝ)) =
      Module.finrank ℝ (LinearMap.ker (T ∘ₗ E)) := by
    rw [← hmap]; exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE _)).symm
  rw [Module.finrank_fin_fun] at h1 h2
  have heq := Submodule.eq_of_le_of_finrank_le
    (inf_le_right : LinearMap.range E ⊓ LinearMap.ker T ≤ LinearMap.ker T) (by omega)
  rw [← hrE, ← heq]; exact inf_le_left

theorem gramQ {r r₀ : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ) :
    (Matrix.of fun i j => (A i j : ℝ)) * (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun i j => (A i j : ℝ))ᵀ
      = (Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k).map (Int.cast : ℤ → ℝ) := by
  ext i k
  simp [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem coisotropic_of_torsion_count (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ)
    (A : Fin r₀ → Fin r → ℤ) (hM : M.det ≠ 0)
    (hA : LinearIndependent ℚ (fun i j => (A i j : ℚ)))
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i))
    (v : Fin r → ℝ)
    (hv : ∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) :
    v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  classical
  set Ar : Matrix (Fin r₀) (Fin r) ℝ := Matrix.of fun i j => (A i j : ℝ) with hAr
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set P : Matrix (Fin r₀) (Fin r₀) ℤ := Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k with hP
  have hAz : ((Matrix.of A) * (Matrix.of A)ᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero ((Matrix.of A).map (Int.cast : ℤ → ℚ))
      (vecMul_eq_zero_of_rows_li ((Matrix.of A).map (Int.cast : ℤ → ℚ)) hA)
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  have hArli : LinearIndependent ℝ (fun i => Ar i) := by
    apply rows_li_of_vecMul
    intro y hy
    have hdet : (Ar * Arᵀ).det ≠ 0 := by
      have : Ar = (Matrix.of A).map (Int.cast : ℤ → ℝ) := rfl
      rw [this, gram_map, det_map_intCast]; exact_mod_cast hAz
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← vecMul_vecMul, hy, zero_vecMul]
  have hMu : IsUnit Mr.det := by
    rw [hMr, det_map_intCast]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hM)
  have hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀ := by
    rw [hAr, hMr, gramQ]
    apply rank_bound P
    intro N hN
    haveI : NeZero N := ⟨hN.ne'⟩
    obtain ⟨S, hc, hS'⟩ := hS N hN
    refine ⟨S, hc, fun x hx => ?_⟩
    funext k
    set a : Fin r₀ → ℤ := fun i => ((x i).val : ℤ) with ha_def
    have ha : (fun j => (a j : ZMod N)) = x := by funext j; simp only [a]; rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdv := hS' a (Pi.single k 1) (by rw [ha]; exact hx)
    have hsum : (∑ i, (Pi.single k (1 : ℤ) : Fin r₀ → ℤ) i • A i) = A k := by
      simp [Pi.single_apply]
    rw [hsum] at hdv
    have hvs : ∑ i, a i • A i = a ᵥ* Matrix.of A := (vecMul_eq_sum _ _).symm
    have hz : (∑ i, a i • A i) ⬝ᵥ M *ᵥ A k = (P *ᵥ a) k := by
      rw [hvs, ← dotProduct_mulVec, dotProduct_comm]; rfl
    rw [hz] at hdv
    have hcast := RingHom.map_mulVec (Int.castRingHom (ZMod N)) P a k
    have e1 : (((P *ᵥ a) k : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdv
    simp only [Int.coe_castRingHom, e1] at hcast
    have h2 : (Int.cast ∘ a : Fin r₀ → ZMod N) = x := ha
    rw [h2] at hcast
    exact hcast.symm
  have hker : v ∈ LinearMap.ker (Ar * Mrᵀ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    rw [← mulVec_mulVec, mulVec_transpose]
    have := hv i
    rw [dotProduct_mulVec, dotProduct_comm] at this
    exact this
  exact ker_le_span Mr Ar hMu hArli hρ hker

end GlobalTheory.CoisoCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCountStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coisotropic_sublattice_of_torsion_count : ∀ (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ), M.det ≠ 0 → LinearIndependent ℚ (fun i j => (A i j : ℚ)) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i)) → ∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  first | exact @GlobalTheory.CoisoCount.coisotropic_of_torsion_count | exact GlobalTheory.CoisoCount.coisotropic_of_torsion_count | (intros; apply GlobalTheory.CoisoCount.coisotropic_of_torsion_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenDecompositionVectorBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EigenFrames
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.LB (resG_resG le_iSup_inf)

variable {X : Scheme.{0}} {F G : X.Modules}

theorem isFrame_mkSec (N : Sub F) {U : X.Opens} {ν : Type} [Fintype ν] (e : ν → Γ(F, U))
    (he : ∀ i, e i ∈ N.sec U)
    (hli : ∀ (V : X.Opens) (h : V ≤ U), LinearIndependent Γ(X, V) fun i => resM F h (e i))
    (hsp : ∀ (V : X.Opens) (h : V ≤ U) (x : Γ(F, V)), x ∈ N.sec V →
      x ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i))) :
    GlobalTheory.VB.IsFrame (F := N.toMod) fun i => N.mkSec (e i) (he i) := by
  rw [GlobalTheory.VB.isFrame_iff]
  intro V h
  have hcomp : (appLinear N.incl V) ∘ (fun i => resM N.toMod h (N.mkSec (e i) (he i))) =
      fun i => resM F h (e i) := funext fun i => by
    simp only [Function.comp, appLinear_apply]
    rw [app_resM]
    rfl
  refine ⟨LinearIndependent.of_comp (appLinear N.incl V) (hcomp ▸ hli V h), ?_⟩
  rintro y -
  have hx := hsp V h _ (N.incl_app_mem y)
  rw [← hcomp, Set.range_comp, Submodule.span_image] at hx
  obtain ⟨y', hy', e'⟩ := hx
  have : y' = y := N.incl_app_injective V (by rwa [appLinear_apply] at e')
  exact this ▸ hy'

section Frames

variable {O : Type} [CommRing O] (ρ : O →+* CategoryTheory.End F) {κ : Type} [Fintype κ]
  (τ : κ → (O →+* Γ(X, ⊤))) {m : κ → ℕ} {U : X.Opens} (B : (Σ i, Fin (m i)) → Γ(F, U))
  (hB : GlobalTheory.VB.IsFrame B)
  (hact : ∀ i k a, (act ρ a).app U (B ⟨i, k⟩) = resG X (le_top : U ≤ ⊤) (τ i a) • B ⟨i, k⟩)

end Frames

end GlobalTheory.EigenFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isLatBasis_of_isLatFam : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  intro n g B K b₀ hK hb₀
  obtain ⟨H, hH⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH]; exact H.zero_mem
  obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hcont : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hev : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ K b₀ → w = 0 := by
    filter_upwards [hcont.eventually hζ] with w hw hwK
    rw [← hζ0]; exact hw.1 hwK
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule H
  have hL : ∀ w, w ∈ L ↔ w ∈ K b₀ := fun w => by
    rw [← hH]; rfl
  haveI : DiscreteTopology L := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.1 hev
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Subtype.val ⁻¹' U := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h0U
      · intro hx; exact Subtype.ext (hU hx ((hL x).1 x.2))
    rw [this]; exact hUo.preimage continuous_subtype_val
  let bs := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, fun i => (bs i : Fin g → ℂ), GlobalTheory.linearIndependent_real_coe_basis bs, fun w => ?_⟩
  have hsp := GlobalTheory.span_range_coe_basis bs
  have hw : w ∈ L ↔ w ∈ Submodule.span ℤ (Set.range fun i => (bs i : Fin g → ℂ)) := by rw [hsp]
  rw [← hL, hw, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_independent_basis_lattice_family : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | exact GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

end GlobalTheory.AmpleOverBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

theorem inner_theta_eq_lam : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring

end GlobalTheory.Mem.R3.LamMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam | exact GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam | (intros; apply GlobalTheory.Mem.R3.LamMetric.inner_theta_eq_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

theorem readPk_pin_exists : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ (s : Side0 o) (r : ReadPk m s), r.Pin := by
  intro B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_side_reading_level_zero_moved B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := GlobalTheory.T.exists_reading_in_movedRowData B f T w Z₀ hX Wt z₀ q o hIn hF m s
  obtain ⟨Z⟩ := hs Y h2 h9 h10 h11
  exact ⟨s, ⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11, h12⟩⟩

end GlobalTheory.Mem.R3.Rw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reading_of_rowLiftFamily_movedData : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ (s : Side0 o) (r : ReadPk m s), r.Pin := by
  first | exact @GlobalTheory.Mem.R3.Rw.readPk_pin_exists | exact GlobalTheory.Mem.R3.Rw.readPk_pin_exists | (intros; apply GlobalTheory.Mem.R3.Rw.readPk_pin_exists <;> assumption)
end
end

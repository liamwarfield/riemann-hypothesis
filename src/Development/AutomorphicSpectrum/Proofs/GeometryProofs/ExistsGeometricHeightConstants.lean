module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspHeightUpper
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
public import Development.WeilBound.CoreStatements.VolumeEquality.PiecesOf
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeets
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRoots
public import Development.WeilBound.CoreStatements.VolumeEquality.LocInj
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
public import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightBoundFullIntersectionSystem
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresScaledLattice
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresBlockEmbedding
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HodgeCompactCoverPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBound

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesExistence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

theorem SheetDecomposition.sheet_pieces_existence : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), Nonempty (Pieces Or) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  exact SheetDecomposition.pieces_of Or SheetDecomposition.holNull SheetDecomposition.chartMeets SheetDecomposition.rootBranches SheetDecomposition.coverRoots SheetDecomposition.locInj SheetDecomposition.baseUnifEx hG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeUpper
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSigns
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLines
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLines
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

theorem nefOnFibres_of_wt {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (n : Ψ × Fin N → ℤ)
    (h : ∀ p : ℕ, p.Prime → M.NefAt p (fun τ i => -(n (τ, i) : ℝ)) 0) :
    NefOnFibres (mCoordIdeal M.y) (∑ r, n r • M.xdeg r) := by
  intro W h1 h2 h3 h4
  obtain ⟨d, -, he⟩ := LevelTowerAlt.geoNum_one_lin W
  have h5 := h _ (PB.prime_charOf_of_ne_zero h1.1 h3) W ⟨h1, h2, rfl, h4⟩
  unfold Top.RootModel.curveDeg at h5
  rw [Fintype.sum_option] at h5
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, neg_neg, M.x_deg, he] at h5
  rw [he]
  have : ∑ k, (∑ r, n r • M.xdeg r) k * d k = ∑ r, n r * ∑ k, M.xdeg r k * d k := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [_root_.mul_assoc]
  rw [this]
  exact_mod_cast h5

theorem nefThreshold_of_gap_one {Ψ : Type} [Fintype Ψ] {N j : ℕ} (mu : Top.Wt Ψ N) (b : ℕ) (hb : 4 * Fintype.card Ψ + 2 ≤ b)
    (h1 : ∀ τ i, |mu τ i| ≤ 1) (h2 : ∀ τ, Top.gap j mu τ = 1) : Top.NefThreshold j b mu := by
  intro τ
  have hn : ‖mu‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 τ i
  have hb' : 4 * (Fintype.card Ψ : ℝ) + 2 ≤ b := by exact_mod_cast hb
  rw [h2]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Ψ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  intro hG E _ _ _ H D Xo l c Y S _ M 𝔐 Fl e hY hp hq hS hS' hR
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  have key : ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → (∀ τ i, |mu τ i| ≤ 1) →
      (∀ τ, Top.gap D.p mu τ = 1) → ∀ r : ℕ, r.Prime → M.NefAt r mu 0 := by
    intro mu hd h1 h2 r hr
    by_cases hrS : r ∈ S
    · exact GlobalTheory.T.root_lines_weight_bound_of_free hG.2.2.2.2.2.2.1 E H D l (Xo l) c _ _ Y S M 𝔐 Fl e r hrS (hS r hrS) hR mu hd
    · obtain ⟨a1, a2, a3⟩ := hS' r hr hrS
      exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
        l c hg Y hdom hp hq S M 𝔐 Fl e hR r hr a3 hrS a1 mu hd (GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefThreshold_of_gap_one mu r a2 h1 h2)
  have g1 : D.p - 1 < D.p + D.q := by omega
  have g2 : D.p < D.p + D.q := by omega
  have g3 : ¬ D.p ≤ D.p - 1 := by omega
  have g4 : D.p - 1 < D.p := by omega
  constructor
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if D.p ≤ (r.2 : ℕ) then 1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, one_smul, zero_smul]
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g3]
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if (r.2 : ℕ) < D.p then -1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, neg_smul, one_smul, zero_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g4]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLinesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | exact GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | (intros; apply GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  first | exact @LevelTowerAlt.hodge_compact_cover_primes | exact LevelTowerAlt.hodge_compact_cover_primes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @LevelTowerAlt.nef_fibres_block_embedding | exact LevelTowerAlt.nef_fibres_block_embedding
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | exact GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.coords_reindex_degree <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetNef

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uMul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) :=
  ⟨zpow_ne_zero _ ha.1, TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 n, by
    rw [← zpow_neg]; exact TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 _⟩

theorem uProd {I : Type} [Fintype I] {f : I → Ω} (h : ∀ i, unitAt ξ p (f i)) : unitAt ξ p (∏ i, f i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i).1, prod_mem fun i _ => (h i).2.1, by
    rw [← Finset.prod_inv_distrib]; exact prod_mem fun i _ => (h i).2.2⟩

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨u, h1, h2, h3⟩ := TensDeg.exists_unit_of_span_eq (regAt ξ p) ht.1 (hs.2.symm.trans ht.2)
  have : s / t = u := by rw [h3, mul_div_cancel_right₀ _ ht.1]
  exact ⟨div_ne_zero hs.1 ht.1, this ▸ h1, this ▸ h2⟩

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  have hs : s ≠ 0 := fun h => hu.1 (by rw [h, zero_div])
  have ht0 := ht.1
  refine ⟨hs, ht.2.trans (le_antisymm ?_ ?_)⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.2⟩, ?_⟩
    show (s / t)⁻¹ * s = t
    field_simp
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, ?_⟩
    show (s / t) * t = s
    field_simp

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  have hex : ∃ s, Λ.IsGenAt p s := by
    by_contra h0
    have h1 : Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p = ⊥ := by
      rw [Lat.tens, Submodule.span_eq_bot]
      rintro _ ⟨s, hs, -⟩
      exact absurd ⟨_, hs ()⟩ h0
    have h2 := h.2
    rw [h1, eq_comm, Submodule.span_singleton_eq_bot] at h2
    exact h.1 h2
  obtain ⟨s, hs⟩ := hex
  have h1 := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => σ) p (fun _ => s) fun _ => hs
  have h2 := uZpow (gen_unit h h1) σ
  refine gen_of_unit hs ?_
  convert h2 using 1
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [div_zpow, ← zpow_mul, hσ, zpow_one]

theorem gen_scale {Λ : Lat ξ Ω} {t u : Ω} (hu : u ≠ 0) (h : Λ.IsGenAt p t) : (Λ.scale u).IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero hu h.1, ?_⟩
  show (Λ p).map _ = _
  rw [h.2, Submodule.map_span, Set.image_singleton]
  rfl

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

theorem chart_ratio {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K)
    (x : J k) : y ⟨k, x⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k x)
  dsimp only at h1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k] at h1
  · simpa using h1
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (chart_ne h b)]
  · simp

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

theorem deg_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {a : K → ℤ} {e : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsDegOn Set.univ y a e) :
    Λ.IsDegOn Set.univ y (σ • a) (e ^ σ) := by
  refine ⟨zpow_ne_zero _ h.1, fun q _ c hc => ?_⟩
  have h1 := (gen_untens hσ (deg_gen h hc)).2
  rw [h1, mul_zpow, ← Finset.prod_zpow]
  simp only [Pi.smul_apply, smul_eq_mul, ← zpow_mul, mul_comm σ]

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) :=
  ⟨(map_ne_zero i).2 h.1, hreg _ h.2.1, by rw [← map_inv₀]; exact hreg _ h.2.2⟩

theorem frame_pull {L : Lat ξ V} {r : ℕ} {b : Fin r → V} (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : LinearIndependent Ω' fun k => j (b k)) {q : Cpt ξ'} (h : genPt ξ ⤳ f q.1)
    (hreg : ∀ a ∈ regAt ξ ⟨f q.1, h⟩, i a ∈ regAt ξ' q) (hb : L.IsFrameAt b ⟨f q.1, h⟩) :
    (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) q := by
  refine ⟨hli, ?_⟩
  have hL := hb.2
  have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q.1, h⟩) (Set.range b),
      j e ∈ Submodule.span (regAt ξ' q) (Set.range fun k => j (b k)) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q) • j x := hj a x
      rw [e1]
      exact Submodule.smul_mem _ _ hx
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h3, e, he, rfl⟩
    exact key' e (by rw [← hL]; exact he)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨h, b k, ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

theorem det_pull {L : Lat ξ V} {r m : ℕ} {s : Fin m → V} {U : Submodule Ω V} (hd : Dominates ξ' ξ f i)
    (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k))
    (hs : LinearIndependent Ω s) (hsU : Submodule.span Ω (Set.range s) = U) (hL : L.IsVB r U)
    {b₀ : Fin r → V'} (hb₀ : LinearIndependent Ω' b₀) (hF : (L.pull ξ' f j).IsFlagVBOn Set.univ b₀) :
    ∃ u : Ω', u ≠ 0 ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (u * i t) := by
  let g : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  obtain ⟨hg, hgreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd g
  obtain ⟨U₀, hU₀, b, hb, hfr⟩ := hL ⟨f g.1, hg⟩ trivial
  have hbf := hfr _ trivial hU₀
  have hrm : r = m := by
    have h1 := finrank_span_eq_card hs
    have h2 := finrank_span_eq_card hbf.1
    rw [hsU] at h1
    rw [hb] at h2
    simpa using h2.symm.trans h1
  subst hrm
  have hjb : ∀ k, j (b k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨U₁, hU₁, b', hb', hfr'⟩ := hF g trivial
    have e1 : ∀ c : Fin r → V', flagStep Ω' c r = Submodule.span Ω' (Set.range c) := fun c => by
      unfold flagStep
      congr 1
      ext x
      simp
    rw [← e1, ← hb', e1]
    have h1 : j (b k) ∈ (L.pull ξ' f j) g := by
      rw [(frame_pull hj (hli _ _ hbf.1) hg hgreg hbf).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [(hfr' g trivial hU₁).2] at h1
    exact Submodule.span_le_restrictScalars (regAt ξ' g) Ω' _ h1
  have hjs : ∀ k, j (s k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := s) (s := b) fun k => by
      rw [hb, ← hsU]; exact Submodule.subset_span ⟨k, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT k, map_sum]
    exact Submodule.sum_mem _ fun k' _ => by rw [hj]; exact Submodule.smul_mem _ _ (hjb k')
  obtain ⟨T₁, hT₁⟩ := exists_mat hjs
  have main : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
    intro q h
    obtain ⟨_, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
    obtain ⟨U₂, hU₂, c, hc, hcf⟩ := hL ⟨f q.1, h⟩ trivial
    have hcf' := hcf _ trivial hU₂
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := c) (s := s) fun k => by
      rw [hsU, ← hc]; exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨T.det, GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X Ω ξ V L r s c T _ hs hcf' hT, ?_⟩
    have h2 := GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X' Ω' ξ' V' (L.pull ξ' f j) r b₀ (fun k => j (c k)) (T₁ * i.mapMatrix T) q hb₀
      (frame_pull hj (hli _ _ hcf'.1) h hreg hcf') fun k => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hT k, map_sum]
        simp only [hj, hT₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        rw [Finset.sum_comm]
        simp only [mul_comm]
    rwa [Matrix.det_mul, ← RingHom.map_det] at h2
  obtain ⟨t, -, ht⟩ := main g hg
  exact ⟨T₁.det, left_ne_zero_of_mul ht.1, main⟩

theorem deg_pull {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : Dominates ξ' ξ f i)
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    {K' : Type} [Fintype K'] {J' : K' → Type} {y' : (Σ k, J' k) → Ω'} {bk : K → K'} {bx : ∀ k, J k ≃ J' (bk k)}
    (hbk : Function.Injective bk) (hy : ∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) {a : K → ℤ} {a' : K' → ℤ}
    (ha : ∀ k, a' (bk k) = a k) (ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0) {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    ((Lat.tens Λ' fun _ => -1).scale (∏ τ, u τ)).IsDegOn Set.univ y' a' (i e₀) := by
  refine ⟨(map_ne_zero i).2 h.1, fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨c, hc⟩ := hcov ⟨f q.1, hq⟩
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := gen_scale (Finset.prod_ne_zero_iff.2 fun τ _ => hu τ : ∏ τ, u τ ≠ 0)
    (Flag.tens_gen Λ' (fun _ => -1) q _ ht')
  have g3 : ∀ k, unitAt ξ' q (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) := fun k => by
    refine ⟨div_ne_zero (chart_ne hc' _) ((map_ne_zero i).2 (chart_ne hc k)), ?_, ?_⟩
    · have := hreg _ (chart_ratio hc k ((bx k).symm (c' (bk k))))
      rwa [map_div₀, ← hy, Equiv.apply_symm_apply] at this
    · rw [inv_div, ← hy]
      exact chart_ratio hc' _ _
  have g4 := uMul (uProd fun k => uZpow (g3 k) (a k)) g1
  have e1 : ∏ k', y' ⟨k', c' k'⟩ ^ a' k' = ∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k := by
    symm
    refine Fintype.prod_of_injective bk hbk _ _ (fun k' hk' => ?_) fun k => by rw [ha]
    rw [ha' k' hk', zpow_zero]
  have e2 : (∏ τ, u τ) * ∏ τ, (u τ * i (t τ)) ^ (-1 : ℤ) = i (∏ τ, t τ ^ (-1 : ℤ)) := by
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := hu τ
    rw [map_zpow₀, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv_cancel_left₀ this]
  rw [e2] at g2
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ a' k') * i e₀) g2 ?_).2
  convert g4 using 1
  have e3 : i (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k))
  have e4 : ∏ k, (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) ^ a k =
      (∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k) / i (∏ k, y ⟨k, c k⟩ ^ a k) := by
    rw [map_prod, ← Finset.prod_div_distrib]
    simp only [div_zpow, map_zpow₀]
  rw [e1, e4, map_div₀, map_mul, ← mul_div_assoc, ← _root_.mul_assoc, div_mul_cancel₀ _ e3]

end GlobalTheory.CompanionTheory.Ar.Cusp.DetNef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefDegreeScaleInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  first | exact @LevelTowerAlt.nef_fibres_scaled_lattice | exact LevelTowerAlt.nef_fibres_scaled_lattice
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSigns
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  intro hG hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 dg sm m s a e₀ hY hp hq hcov hS hS' hsm hs hdeg
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  obtain ⟨M, 𝔐', Fl, e, i, g, bk, bx, j, hbk, hy, hd, hS2, hR, hj, hli, hV⟩ :=
    GlobalTheory.T.hodge_comp_cover_primes hW E H D Xo l c Y S Ω K J y 𝔐 dg hcov
      (fun p hp hdv => by by_contra h; exact (hS' p hp h).1 hdv) hS
  haveI : CharZero M.Ω := charZero_of_injective_ringHom i.injective
  have hNef : _ ∧ _ :=
    GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines hG E H D Xo l c Y S M 𝔐' Fl e
      hY hp hq hS2 hS' hR
  obtain ⟨n1, n2⟩ := hNef
  have hb₀ : ∀ σ, LinearIndependent M.Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  have hu := fun τ => GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.det_pull (L := 𝔐.V (sm τ)) hd hj hli (hs τ).1 (hs τ).2 (𝔐.vb (sm τ)) (hb₀ (sm τ))
    (by rw [← hV]; exact Fl.sub (sm τ))
  choose u hu0 hu using hu
  let a' : M.K → ℤ := Function.extend bk a 0
  have ha : ∀ k, a' (bk k) = a k := fun k => hbk.extend_apply _ _ k
  have ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0 := fun k' h => Function.extend_apply' _ _ _ h
  have hB := GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_pull hu0 hd 𝔐.tie.cover hu hbk hy ha ha' hdeg
  simp only [← hV] at hB
  have hgr : ∀ (r : CMType H × Fin (D.p + D.q)) (σ : Σ s, Fin (labelRk D s)), HodgeCpt.rootIdx D r = σ →
      ((𝔐'.V σ.1).gr (Fl.b σ.1) σ.2).IsDegOn Set.univ M.y (HodgeCpt.rootSgn D r • M.xdeg r)
        (e r ^ HodgeCpt.rootSgn D r) := by
    rintro r _ rfl
    refine GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_untens ?_ (hR r)
    unfold HodgeCpt.rootSgn
    split_ifs <;> norm_num
  have hA : ∃ A e₁, (Lat.tens (fun τ => detLat (𝔐'.V (sm τ)) (Fl.b (sm τ))) fun _ => -1).IsDegOn Set.univ M.y A e₁ ∧
      NefOnFibres (mCoordIdeal M.y) A := by
    have hdet : ∀ σ, detLat (𝔐'.V σ) (Fl.b σ) = Lat.tens (fun k => (𝔐'.V σ).gr (Fl.b σ) k) fun _ => 1 := fun σ =>
      GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ σ) (Fl.sub σ)
    simp only [hdet]
    rcases hsm with rfl | rfl
    · have h1 : ∀ τ (k : Fin D.p), HodgeCpt.rootIdx D (τ, Fin.castAdd D.q k) = ⟨.inl τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_left (show ((Fin.castAdd D.q k : Fin _) : ℕ) < D.p from k.2)]
        rfl
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n2 using 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      simp [HodgeCpt.rootSgn]
    · have h1 : ∀ τ (k : Fin D.q), HodgeCpt.rootIdx D (τ, Fin.natAdd D.p k.rev) = ⟨.inr τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_right (by simp)]
        congr 1
        apply Fin.ext
        have := k.2
        simp only [Fin.val_natAdd, Fin.val_rev]
        omega
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n1 using 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      have h2 : ∀ k : Fin D.p, ¬ D.p ≤ (k : ℕ) := fun k => not_le.2 k.2
      have h3 := Equiv.sum_comp Fin.revPerm fun k : Fin D.q => M.xdeg (τ, Fin.natAdd D.p k)
      simp [HodgeCpt.rootSgn, h2, ← h3]
  obtain ⟨A, e₁, hA1, hA2⟩ := hA
  have hN := GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant hI _ M.Ω M.K M.ι M.y 𝔐'.ξ _ A a' e₁ _ _ 𝔐'.tie
    (Finset.prod_ne_zero_iff.2 fun τ _ => hu0 τ) hA1 hB hA2
  obtain ⟨c₀, hc₀⟩ := 𝔐'.tie.cover ⟨genPt 𝔐'.ξ, specializes_rfl⟩
  exact GlobalTheory.T.coords_reindex_degree hI Ω M.Ω i K M.K J M.ι y M.y bk bx a a' hbk hy (fun k => ⟨_, GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.chart_ne hc₀ k⟩) ha ha' hN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSignsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeUpper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem span_eq_of_card_nef {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {m r : ℕ} {s : Fin m → V} {b : Fin r → V}
    {U : Submodule Ω V} (hs : LinearIndependent Ω s) (hb : LinearIndependent Ω b)
    (hU : Submodule.span Ω (Set.range b) = U) (hm : ∀ k, s k ∈ U) (h : r = m) :
    Submodule.span Ω (Set.range s) = U := by
  subst hU
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b)) := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hm k
  · rw [finrank_span_eq_card hs, finrank_span_eq_card hb]
    simp [h]

end GlobalTheory.CompanionTheory.Ar.Cusp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_upper : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ), admitted Xo l c Y Or B₁ → 4 * Dc.f + 2 ≤ B → NefOnFibres (mCoordIdeal Dc.y) (muTwDeg Hd B) := by
  intro hG hW E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ B hA hB
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨hY, hgood, hS₀, -, hB₁, hS, -⟩ := hA
  obtain ⟨v1, v2, v3, v4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  let g : Cpt Or.𝔐.ξ := ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨ch, hch⟩ := Or.𝔐.tie.cover g
  obtain ⟨m, f, cc, -, -, hsum, hl⟩ := Hd.locally ch hch.1
  have hm : Nonempty (Fin m) := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    simp at hsum
  obtain ⟨bb, -, u, -, hΛ⟩ := hl hm.some
  have hs : ∀ τ k, ∃ s : Or.𝔐.Li, s ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have h1 : Or.i τ (bb τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact LinearMap.mem_range_self _ _
    obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 h1
    exact ⟨z, hz, by rw [← hxz, add_sub_cancel_right]; exact hx⟩
  choose s hs using hs
  obtain ⟨w1, w2⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hspan : ∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = Or.𝔐.Vgen (Or.sm τ) := fun τ => by
    obtain ⟨U, hU, b, hb, hfr⟩ := v4 (Or.sm τ) g trivial
    exact ⟨w1 τ, GlobalTheory.CompanionTheory.Ar.Cusp.span_eq_of_card_nef (w1 τ) (hfr g trivial hU).1 hb (fun k => (hs τ k).1) (Or.rk_sm τ)⟩
  have hj1 := Dc.one_le_j
  have hj2 := Dc.j_le
  have hj3 := Dc.two_le_N
  have hN := Or.N_eq
  have hpq : 1 ≤ D.p ∧ 1 ≤ D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hside : Or.sm = Sum.inl ∨ Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact .inr h
    · exact .inl h
  refine GlobalTheory.T.hodge_comp_cover_cm_signs hG hW E H D Xo l c Y (S₀ ∪ Dc.SB B) Ω K J Dc.y (Or.𝔐.withS _ v1 v2 v3 v4) Or.deg Or.sm _ s _ _
    hY hpq.1 hpq.2 Or.cover (fun p hp => ?_) (fun p hp hpS => ?_) hside hspan w2
  · rcases Finset.mem_union.1 hp with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  · rw [Finset.mem_union, not_or] at hpS
    have h1 : ¬ (p : ℤ) ∣ 2 * discr E * l.M' := fun h => hpS.1 ((hS₀ p).2 ⟨hp, h⟩)
    have h2 : 4 * Dc.f + 2 ≤ p := by
      by_contra h
      exact hpS.2 (Finset.mem_filter.2 ⟨(hS p).2 ⟨hp, by omega, hpS.1⟩, by omega⟩)
    refine ⟨fun h => h1 ((h.mul_left 2).mul_right _), h2, lt_of_le_of_ne hp.two_le ?_⟩
    rintro rfl
    exact h1 ((Dvd.intro _ rfl : ((2 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * discr E).mul_right _)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeUpperStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_degree_upper : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ), admitted Xo l c Y Or B₁ → 4 * Dc.f + 2 ≤ B → NefOnFibres (mCoordIdeal Dc.y) (muTwDeg Hd B) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_degree_upper | exact GlobalTheory.CompanionTheory.Relay.intersection_degree_upper | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_degree_upper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_lower : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → S'.IsTied → PosU S' := by
  intro hG hW E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hA hT
  exact GlobalTheory.T.posU_of_full_intersection_system hG.2.2.2.2.2.2.2.2.2.1 K J II _ Ω W Dc Hd M _ S' hII hT fun B hB =>
    GlobalTheory.T.intersection_degree_upper hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ B hA hB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_degree_lower : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → S'.IsTied → PosU S' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_degree_lower | exact GlobalTheory.CompanionTheory.Relay.intersection_degree_lower | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_degree_lower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem pieces_nonempty : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), Nonempty (Pieces Or) :=
  @SheetDecomposition.sheet_pieces_existence

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_left : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), Nonempty (Pieces Or) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.pieces_nonempty | exact GlobalTheory.CompanionTheory.Ar.Cusp.pieces_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.pieces_nonempty <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem ptsIntegral_eq_sum_fundamental : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t :=
  SheetDecomposition.sheet_pieces_component

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace TopMean

theorem bracket_le (f j' B : ℕ) (rd L : ℝ) (hrd : 2 ≤ rd) (hf : 1 ≤ f) (hj : 1 ≤ j')
    (hB : 2 * f * j' ≤ B) (hB64 : 64 ≤ B) :
    6 + Real.log (2 * (f : ℝ) * rd) + Real.log (2 * (f : ℝ) * j' * rd) ≤
      4 * (Real.log ((B : ℝ) * rd) + |L|) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  have hB' : 2 * (f : ℝ) * j' ≤ B := by exact_mod_cast hB
  have hB64' : (64 : ℝ) ≤ B := by exact_mod_cast hB64
  have hrd0 : 0 < rd := by linarith
  have h1 : Real.log (2 * (f : ℝ) * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right _ hrd0.le
    nlinarith
  have h2 : Real.log (2 * (f : ℝ) * j' * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hB' hrd0.le
  have h3 : 3 ≤ Real.log ((B : ℝ) * rd) := by
    have h128 : (128 : ℝ) ≤ (B : ℝ) * rd := by nlinarith
    have hl : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h128
    have := Real.log_two_gt_d9
    linarith
  have := abs_nonneg L
  linarith

end TopMean


open TopMean in
theorem top_mean_cusp_weight : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  intro hG
  refine ⟨4, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U _ _ hU
  obtain ⟨Q⟩ := GlobalTheory.T.cusp_volume_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨κ, hκ, htr⟩ := GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q
  have hw := GlobalTheory.T.cusp_volume_middle E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q U hU
  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  intro hj' hN B hB
  have hjN : Dc.j + Dc.j' = Dc.N := by
    have := Dc.j_le; have := Dc.two_le_N
    show Dc.j + (Dc.N - Dc.j) = Dc.N
    omega
  have hball := fun k => GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E (CMType H) Dc.j Dc.j' Dc.n Q.g (Q.Λ k) H (Q.F k) (Q.Γ k) (Q.FF k)
    (Q.arith k) (Q.fund k) hj' (by omega)
  set C : ℝ := (Fintype.card (CMType H) : ℝ) * Dc.j' * (6 + Real.log (2 * Fintype.card (CMType H) * hostRd E) +
    Real.log (2 * Fintype.card (CMType H) * Dc.j' * hostRd E)) with hC
  have hdeg : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
        ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) (fun _ => 1) := rfl
    rw [e1, htr (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun k => by simpa using (hball k).1)]
    refine congrArg (κ * ·) (Finset.sum_congr rfl fun k _ => ?_)
    simp
  have hnum : ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t :=
    htr U (fun k t => ((Q.F k).R t).cuspW (Q.F k).σ) hw.1 hw.2 (fun k => (hball k).2.2.1)
  have hle : ∀ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t) ≤
      C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) := fun k => by
    have h := mul_le_mul_of_nonneg_left (hball k).2.2.2 (Nat.cast_nonneg (α := ℝ) (Q.d k))
    calc _ ≤ _ := h
      _ = _ := by rw [hC]; ring
  have hDpos : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
    rw [hdeg]
    apply mul_pos hκ
    obtain ⟨k0, hk0⟩ := Q.d_pos
    exact Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hball k).2.1.le)
      ⟨k0, Finset.mem_univ _, mul_pos (by exact_mod_cast hk0) (hball k0).2.1⟩
  have hmean : meanOf Hd U ≤ C := by
    unfold meanOf
    rw [div_le_iff₀ hDpos, hnum]
    calc κ * ∑ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t)
        ≤ κ * ∑ k, C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) hκ.le
      _ = C * GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
          rw [hdeg, ← Finset.mul_sum]; ring
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hfD : Dc.f = Fintype.card (CMType H) := rfl
  have hN4 : 4 ≤ Dc.N := by omega
  have hB64 : 64 ≤ B := by
    have : 4 * 1 * 4 ^ 2 ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]; gcongr
    omega
  have hB2 : 2 * Fintype.card (CMType H) * Dc.j' ≤ B := by
    have hjN' : Dc.j' ≤ Dc.N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have : 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]
      calc 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2 := by
            have := Nat.mul_le_mul_left (4 * Fintype.card (CMType H)) hjN'
            nlinarith
        _ = _ := rfl
    omega
  have hbr := bracket_le (Fintype.card (CMType H)) Dc.j' B (hostRd E) (hostLval H) hrd hf hj' hB2 hB64
  have hfj : (0 : ℝ) ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' := by positivity
  calc meanOf Hd U ≤ C := hmean
    _ ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' * (4 * (Real.log ((B : ℝ) * hostRd E) + |hostLval H|)) := by
        rw [hC]; exact mul_le_mul_of_nonneg_left hbr hfj
    _ = 4 * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
        rw [hfD, GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_sum : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight | exact GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := GlobalTheory.T.cusp_height_upper hG hF
  obtain ⟨Cu, hCu⟩ := GlobalTheory.T.cusp_volume_sum hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨GlobalTheory.T.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_height_constants : Top.Given → Out.WeilSt → Fl.FlatDegree → ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | exact GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.TopNine.nineGeoU_of_given <;> assumption)
end

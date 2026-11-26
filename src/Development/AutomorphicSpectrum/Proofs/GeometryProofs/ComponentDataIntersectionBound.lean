module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThird
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThird
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem gramAt_posDef_of_isFrameAt_blocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ b h hi hf
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hmem : ∀ w, Or.i τ w ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := fun w => by
    rw [← Or.i_range τ]
    exact LinearMap.mem_range_self _ w
  let φ : W τ →ₗ[Ω] ↥(Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)) := (Or.i τ).codRestrict _ hmem
  have hφi : Function.Injective φ := fun x y hxy => Or.i_inj τ (congrArg Subtype.val hxy)
  have hφs : Function.Surjective φ := fun x => by
    have hx : (x : Or.𝔐.Li) ∈ LinearMap.range (Or.i τ) := by
      rw [Or.i_range τ]
      exact x.2
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, Subtype.ext hw⟩
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  have hframe : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p)
      (Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype).IsFrameAt (fun k => φ (b k)) ⟨centre z, h⟩ := by
    refine ⟨hf.1.map' φ (LinearMap.ker_eq_bot.2 hφi), ?_⟩
    have hs := hf.2
    ext x
    obtain ⟨w, rfl⟩ := hφs x
    have hrange : Set.range (fun k => φ (b k)) = φ '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    have hspan : Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range (fun k => φ (b k))) =
        (Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range b)).map
          (φ.restrictScalars (regAt Or.𝔐.ξ ⟨centre z, h⟩)) := by
      rw [hrange, Submodule.map_span]
      rfl
    rw [hspan, ← hs]
    constructor
    · intro hx
      exact ⟨w, hx, rfl⟩
    · rintro ⟨w', hw', e⟩
      have : w' = w := hφi e
      subst this
      exact hw'
  obtain ⟨G, h1, h2⟩ := GlobalTheory.T.pair_sum_frame_at_point E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) Dc.N
    (fun k => φ (b k)) z h hpol hframe
  exact ⟨G, h1, h2⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThirdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | exact GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | (intros; apply GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormal
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem quotNormSq_eq_of_blockFrame : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  intro N j hj G G' T Γ hG hG' hT1 hT2 hT3 hG'1 hG'2
  obtain ⟨e, hel, her⟩ : ∃ e : Fin j ⊕ Fin (N - j) ≃ Fin N,
      (∀ a, e (Sum.inl a) = headIdx hj a) ∧ ∀ k, e (Sum.inr k) = tailIdx hj k :=
    ⟨finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hj)),
      fun a => by ext; simp [headIdx],
      fun k => by ext; simp [tailIdx]⟩
  have hhinj : Function.Injective (headIdx hj) := by
    intro a a' h
    rw [← hel, ← hel] at h
    exact Sum.inl_injective (e.injective h)
  have hht : ∀ a k, headIdx hj a ≠ tailIdx hj k := by
    intro a k h
    rw [← hel, ← her] at h
    exact Sum.inl_ne_inr (e.injective h)
  have hblocks : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.submatrix e e =
      Matrix.fromBlocks (M.submatrix (headIdx hj) (headIdx hj))
        (M.submatrix (headIdx hj) (tailIdx hj))
        (M.submatrix (tailIdx hj) (headIdx hj)) (M.submatrix (tailIdx hj) (tailIdx hj)) := by
    intro M
    ext (a | k) (a' | k') <;> simp [hel, her]
  have hdet : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.det = (M.submatrix e e).det := fun M =>
    (Matrix.det_submatrix_equiv_self e M).symm
  have hTdet : T.det = 1 := by
    have h1 : T.submatrix (headIdx hj) (headIdx hj) = 1 := by
      ext a a'; simp [hT1, Matrix.one_apply]
    have h0 : T.submatrix (tailIdx hj) (headIdx hj) = 0 := by
      ext k a; simp [hT2]
    have h2 : T.submatrix (tailIdx hj) (tailIdx hj) = 1 := by
      ext k k'; simp [hT3, Matrix.one_apply]
    rw [hdet T, hblocks T, h1, h0, h2, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdetG : G'.det = G.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hTdet]
    simp
  have hcol : T.submatrix id (headIdx hj) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix id (headIdx hj) := by
    ext y a'
    obtain ⟨z, rfl⟩ := e.surjective y
    rcases z with a | k
    · simp [hel, hT1, Matrix.one_apply, hhinj.eq_iff]
    · simp [her, hT2, Matrix.one_apply, (hht a' k).symm]
  have key : ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (Mᴴ * G * M).submatrix (headIdx hj) (headIdx hj) =
        (M.submatrix id (headIdx hj))ᴴ * G * M.submatrix id (headIdx hj) := by
    intro M
    first
      | rfl
      | (ext a a'; simp [Matrix.mul_apply, Matrix.conjTranspose_apply])
  have hhh : G'.submatrix (headIdx hj) (headIdx hj) = G.submatrix (headIdx hj) (headIdx hj) := by
    rw [hG', key T, hcol, ← key 1]
    simp
  have hht' : G'.submatrix (headIdx hj) (tailIdx hj) = 0 := by
    ext a k; simp [hG'1]
  have htt : G'.submatrix (tailIdx hj) (tailIdx hj) = Γ := by
    ext k k'; simp [hG'2]
  have hdetblock : G.det = (G.submatrix (headIdx hj) (headIdx hj)).det * Γ.det := by
    rw [← hdetG, hdet G', hblocks G', hht', htt, Matrix.det_fromBlocks_zero₁₂, hhh]
  have hpos : 0 < (G.submatrix (headIdx hj) (headIdx hj)).det :=
    (hG.submatrix hhinj).det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  unfold quotNormSq
  rw [hdetblock, Complex.mul_re, ← him, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ hre.ne'

end GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_matrix_gram_normal : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame | exact GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame.quotNormSq_eq_of_blockFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SmallGram

def blockEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem blockEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : blockEquiv hj (Sum.inl a) = headIdx hj a := by
  ext; simp [blockEquiv, headIdx]

theorem blockEquiv_inr {j N : ℕ} (hj : j ≤ N) (k : Fin (N - j)) : blockEquiv hj (Sum.inr k) = tailIdx hj k := by
  ext; simp [blockEquiv, tailIdx]

theorem sum_blocks {M : Type} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (f : Fin N → M) :
    ∑ p, f p = ∑ a, f (headIdx hj a) + ∑ k, f (tailIdx hj k) := by
  rw [← (blockEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr]

theorem tailIdx_injective {j N : ℕ} (hj : j ≤ N) : Function.Injective (tailIdx hj) := by
  intro a a' h
  rw [← blockEquiv_inr, ← blockEquiv_inr] at h
  simpa using (blockEquiv hj).injective h

def blk {R : Type} [CommRing R] {j N : ℕ} (hj : j ≤ N) (C : Matrix (Fin j) (Fin (N - j)) R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.reindex (blockEquiv hj) (blockEquiv hj) (Matrix.fromBlocks 1 C 0 1)

section GlobalTheory

variable {R : Type} [CommRing R] {j N : ℕ} (hj : j ≤ N) (C : Matrix (Fin j) (Fin (N - j)) R)

theorem blk_hh (a a' : Fin j) : blk hj C (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0 := by
  simp [blk, ← blockEquiv_inl, Matrix.one_apply]

theorem blk_ht (a : Fin j) (k : Fin (N - j)) : blk hj C (headIdx hj a) (tailIdx hj k) = C a k := by
  simp [blk, ← blockEquiv_inl, ← blockEquiv_inr]

theorem blk_th (a : Fin j) (k : Fin (N - j)) : blk hj C (tailIdx hj k) (headIdx hj a) = 0 := by
  simp [blk, ← blockEquiv_inl, ← blockEquiv_inr]

theorem blk_tt (k k' : Fin (N - j)) : blk hj C (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0 := by
  simp [blk, ← blockEquiv_inr, Matrix.one_apply]

theorem det_blk : (blk hj C).det = 1 := by
  simp [blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end GlobalTheory

section Frame

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {j N : ℕ} (hj : j ≤ N)

def replaceTail (b : Fin N → V) (x : Fin (N - j) → V) : Fin N → V :=
  fun p => Sum.elim (b ∘ headIdx hj) x ((blockEquiv hj).symm p)

theorem replaceTail_head (b : Fin N → V) (x : Fin (N - j) → V) (a : Fin j) :
    replaceTail hj b x (headIdx hj a) = b (headIdx hj a) := by
  simp [replaceTail, ← blockEquiv_inl]

theorem replaceTail_tail (b : Fin N → V) (x : Fin (N - j) → V) (k : Fin (N - j)) :
    replaceTail hj b x (tailIdx hj k) = x k := by
  simp [replaceTail, ← blockEquiv_inr]

theorem exists_coeff (A : Subring Ω) {b : Fin N → V} (hb : LinearIndependent Ω b) {x : Fin (N - j) → V}
    (h1 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span A (Set.range b))
    (h2 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span Ω (Set.range (b ∘ headIdx hj))) :
    ∃ C : Matrix (Fin j) (Fin (N - j)) Ω, (∀ a k, C a k ∈ A) ∧
      ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a) := by
  have key : ∀ k, ∃ c : Fin j → Ω, (∀ a, c a ∈ A) ∧ x k = b (tailIdx hj k) + ∑ a, c a • b (headIdx hj a) := by
    intro k
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (h1 k)
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 (h2 k)
    have hz : ∑ p, (((c p : A) : Ω) - Sum.elim c' (fun _ => 0) ((blockEquiv hj).symm p)) • b p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sum_blocks hj (fun p => Sum.elim c' (fun _ => (0 : Ω)) ((blockEquiv hj).symm p) • b p)]
      have e1 : ∑ p, ((c p : A) : Ω) • b p = b (tailIdx hj k) - x k := hc
      simp only [← blockEquiv_inl, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, zero_smul,
        Finset.sum_const_zero, add_zero]
      simp only [blockEquiv_inl]
      rw [e1, sub_eq_zero]
      exact hc'.symm
    have h0 := Fintype.linearIndependent_iff.1 hb _ hz
    have hca : ∀ a, c' a = ((c (headIdx hj a) : A) : Ω) := by
      intro a
      have := h0 (headIdx hj a)
      rw [← blockEquiv_inl] at this
      simp only [Equiv.symm_apply_apply, Sum.elim_inl] at this
      rw [blockEquiv_inl] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun a => - c' a, fun a => ?_, ?_⟩
    · show - c' a ∈ A
      rw [hca]; exact A.neg_mem (c _).2
    · have : ∑ a, (- c' a) • b (headIdx hj a) = - (b (tailIdx hj k) - x k) := by
        rw [← hc']; simp [Finset.sum_neg_distrib]
      rw [this]; abel
  choose C hC hx using key
  exact ⟨Matrix.of fun a k => C k a, fun a k => hC k a, fun k => hx k⟩

variable {b : Fin N → V} {x : Fin (N - j) → V} {C : Matrix (Fin j) (Fin (N - j)) Ω}

include hj in
theorem replaceTail_eq (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) (q : Fin N) :
    replaceTail hj b x q = ∑ p, blk hj C p q • b p := by
  obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective q
  rw [sum_blocks hj]
  rcases u with a' | k'
  · rw [blockEquiv_inl, replaceTail_head]
    simp [blk_hh, blk_th]
  · rw [blockEquiv_inr, replaceTail_tail, hx]
    simp only [blk_ht, blk_tt, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact add_comm _ _

theorem replaceTail_linearIndependent (hb : LinearIndependent Ω b)
    (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) :
    LinearIndependent Ω (replaceTail hj b x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∑ p, ((blk hj C).mulVec g) p • b p = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, replaceTail_eq hj hx, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h0 := Fintype.linearIndependent_iff.1 hb _ h1
  have hdet : (blk hj C).det ≠ 0 := by rw [det_blk]; exact one_ne_zero
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext h0)
  intro i
  exact congrFun this i

theorem span_replaceTail (A : Subring Ω) (hC : ∀ a k, C a k ∈ A)
    (hx : ∀ k, x k = b (tailIdx hj k) + ∑ a, C a k • b (headIdx hj a)) :
    Submodule.span A (Set.range (replaceTail hj b x)) = Submodule.span A (Set.range b) := by
  have hs : ∀ (S : Submodule A V) (k : Fin (N - j)), (∀ a, b (headIdx hj a) ∈ S) →
      ∑ a, C a k • b (headIdx hj a) ∈ S := fun S k h =>
    S.sum_mem fun a _ => S.smul_mem (⟨C a k, hC a k⟩ : A) (h a)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective q
    have hbm : ∀ p, b p ∈ Submodule.span A (Set.range b) := fun p => Submodule.subset_span ⟨p, rfl⟩
    rcases u with a | k
    · rw [blockEquiv_inl, replaceTail_head]; exact hbm _
    · rw [blockEquiv_inr, replaceTail_tail, hx]
      exact add_mem (hbm _) (hs _ k fun a => hbm _)
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    set S := Submodule.span A (Set.range (replaceTail hj b x)) with hS
    have hm : ∀ q, replaceTail hj b x q ∈ S := fun q => Submodule.subset_span ⟨q, rfl⟩
    have hh : ∀ a, b (headIdx hj a) ∈ S := fun a => by simpa [replaceTail_head] using hm (headIdx hj a)
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective p
    rcases u with a | k
    · rw [blockEquiv_inl]; exact hh a
    · rw [blockEquiv_inr]
      have e : b (tailIdx hj k) = x k - ∑ a, C a k • b (headIdx hj a) := by rw [hx]; abel
      rw [e]
      refine sub_mem ?_ (hs S k hh)
      simpa [replaceTail_tail] using hm (tailIdx hj k)

end Frame

end GlobalTheory.CompanionTheory.Ar.SmallGram

namespace GlobalTheory.CompanionTheory.Ar.SmallGram

theorem mem_Vgen_of_mem_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {e : 𝔐.Li} (he : e ∈ 𝔐.V s p) : e ∈ 𝔐.Vgen s := by
  obtain ⟨U, hU, b, hb, hf⟩ := (𝔐.vb s : (𝔐.V s).IsVB (labelRk D s) (𝔐.Vgen s)) p (Set.mem_univ p)
  have h2 : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p (Set.mem_univ p) hU).2
  have hb' : Submodule.span Ω (Set.range b) = 𝔐.Vgen s := hb
  rw [h2] at he
  rw [← hb']
  have hle : Submodule.span (regAt 𝔐.ξ p) (Set.range b) ≤
      (Submodule.span Ω (Set.range b)).restrictScalars (regAt 𝔐.ξ p) :=
    Submodule.span_le.2 Submodule.subset_span
  exact hle he

theorem quotNormSq_eq_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (s : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Submodule.span Ω (Set.range (b ∘ headIdx Dc.j_le_N)) = Hd.F τ → (∀ k, s k ∈ Or.𝔐.Vgen (Or.sm τ)) → (∀ k, Or.i τ (b (tailIdx Dc.j_le_N k)) - s k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩) → (Or.𝔐.V (Or.sm τ)).IsFrameAt s ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → G.PosDef → ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z s Γ ∧ Γ.PosDef ∧ quotNormSq Dc.j_le_N G = Γ.det.re := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ b s h G hI hb hF hs hd hsf hG hGp
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hj := Dc.j_le_N
  have hr : ∀ k, ∃ x, Or.i τ x = s k := fun k => by
    have : s k ∈ LinearMap.range (Or.i τ) := by
      rw [Or.i_range]; exact Submodule.mem_sup_right (hs k)
    exact this
  choose x hx using hr
  have h1 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range b) := by
    intro k
    rw [← hb.2]
    show Or.i τ (b (tailIdx hj k) - x k) ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ ⊔ Or.𝔐.V (Or.sm τ) ⟨centre z, h⟩
    rw [map_sub, hx]
    exact Submodule.mem_sup_left (hd k)
  have h2 : ∀ k, b (tailIdx hj k) - x k ∈ Submodule.span Ω (Set.range (b ∘ headIdx hj)) := by
    intro k
    rw [hF, Or.F_eq, Submodule.mem_comap, map_sub, hx]
    exact mem_Vgen_of_mem_V Or.𝔐 (Or.bg τ) ⟨centre z, h⟩ (hd k)
  obtain ⟨C, hCA, hC⟩ := exists_coeff hj _ hb.1 h1 h2
  have hval : ∀ a k, ∃ r : ℂ, ValAt Or.𝔐.ξ z (C a k) r := by
    intro a k
    obtain ⟨st, hst⟩ := hCA a k
    exact ⟨_, h, st, hst, rfl⟩
  choose Cz hCz using hval
  have hT : ∀ p q, ValAt Or.𝔐.ξ z (blk hj C p q) (blk hj (Matrix.of Cz) p q) := by
    have v0 : ValAt Or.𝔐.ξ z (0 : Ω) (0 : ℂ) := ⟨h, 0, map_zero _, map_zero _⟩
    have v1 : ValAt Or.𝔐.ξ z (1 : Ω) (1 : ℂ) := CxVal.one h
    intro p q
    obtain ⟨u, rfl⟩ := (blockEquiv hj).surjective p
    obtain ⟨u', rfl⟩ := (blockEquiv hj).surjective q
    rcases u with a | k <;> rcases u' with a' | k'
    · simp only [blockEquiv_inl, blk_hh]; split_ifs <;> assumption
    · simp only [blockEquiv_inl, blockEquiv_inr, blk_ht]; exact hCz a k'
    · simp only [blockEquiv_inl, blockEquiv_inr, blk_th]; exact v0
    · simp only [blockEquiv_inr, blk_tt]; split_ifs <;> assumption
  set b' := replaceTail hj b x with hb'
  have hframe : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b'
      ⟨centre z, h⟩ :=
    ⟨replaceTail_linearIndependent hj hb.1 hC, by rw [hb.2, hb', span_replaceTail hj _ hCA hC]⟩
  obtain ⟨G', hG', hG'p⟩ := GlobalTheory.T.component_data_hodge_third E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ b' h hI hframe
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hI
  have hchange : G' = (blk hj (Matrix.of Cz)).conjTranspose * G * blk hj (Matrix.of Cz) :=
    GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z Dc.N (fun k => Or.i τ (b k)) (fun k => Or.i τ (b' k)) G G'
      (blk hj C) (blk hj (Matrix.of Cz)) hpol hG hG'
      (fun q => by rw [hb', replaceTail_eq hj hC, map_sum]; simp only [map_smul]) hT
  obtain ⟨v, hv, hip⟩ := id hG'
  have hhead : ∀ a, Or.i τ (b' (headIdx hj a)) ∈ Or.𝔐.Vgen (Or.bg τ) := by
    intro a
    rw [hb', replaceTail_head]
    have : b (headIdx hj a) ∈ Hd.F τ := by
      rw [← hF]; exact Submodule.subset_span ⟨a, rfl⟩
    rw [Or.F_eq] at this
    exact this
  have htail : ∀ k, Or.i τ (b' (tailIdx hj k)) = s k := fun k => by
    rw [hb', replaceTail_tail, hx]
  have horth : ∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0 := fun a k =>
    GlobalTheory.T.component_data_hodge_fourth E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ _ _ _ _ _ hI (hhead a)
      (by show Or.i τ (b' (tailIdx hj k)) ∈ _; rw [htail]; exact hs k) (hv _) (hv _) (hip _ _)
  refine ⟨G'.submatrix (tailIdx hj) (tailIdx hj),
    ⟨fun k => v (tailIdx hj k), fun k => ?_, fun p q => hip _ _⟩, hG'p.submatrix (tailIdx_injective hj), ?_⟩
  · rw [← htail]; exact hv _
  · exact GlobalTheory.T.block_matrix_gram_normal Dc.N Dc.j hj G G' _ _ hGp hchange (blk_hh hj _) (fun k a => blk_th hj _ a k) (blk_tt hj _)
      horth (fun _ _ => rfl)

end GlobalTheory.CompanionTheory.Ar.SmallGram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (s : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Submodule.span Ω (Set.range (b ∘ headIdx Dc.j_le_N)) = Hd.F τ → (∀ k, s k ∈ Or.𝔐.Vgen (Or.sm τ)) → (∀ k, Or.i τ (b (tailIdx Dc.j_le_N k)) - s k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩) → (Or.𝔐.V (Or.sm τ)).IsFrameAt s ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → G.PosDef → ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z s Γ ∧ Γ.PosDef ∧ quotNormSq Dc.j_le_N G = Γ.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | exact GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | (intros; apply GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeData
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen

theorem gramAt_eq_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ b h G hco hint hfr hG
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, h, hco⟩
  have hnb : w ∉ Dc.Bd := fun hb => (Or.bd z w hco).1 hb hint
  have hex : ∃ a, InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w :=
    (Dc.h τ).cover w ⟨hw, hnb⟩
  have hsib := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ ((Dc.h τ).chart hex.choose)
    ((Dc.h τ).fr hex.choose) ((Dc.h τ).b hex.choose) h hco ((Dc.h τ).isFrame _) hex.choose_spec
  have hmem : ∀ q, b q ∈ Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range ((Dc.h τ).b hex.choose)) := by
    intro q
    rw [← hsib.2, hfr.2]
    exact Submodule.subset_span ⟨q, rfl⟩
  choose cf hcf using fun q => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem q)
  have hS : ∃ S : Matrix (Fin Dc.N) (Fin Dc.N) Ω, ∀ q, b q = ∑ p, S p q • (Dc.h τ).b hex.choose p :=
    ⟨Matrix.of fun p q => (cf q p : Ω), fun q => by rw [← hcf q]; rfl⟩
  have hreg : ∀ p q, hS.choose p q = (cf q p : Ω) := by
    intro p q
    have h0 : ∑ p, (hS.choose p q - (cf q p : Ω)) • (Dc.h τ).b hex.choose p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hS.choose_spec q, sub_eq_zero]
      rw [← hcf q]
      rfl
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hsib.1 _ h0 p)
  choose s hs using fun p q => RingHom.mem_range.1 (cf q p).2
  have hval : ∀ p q, ValAt Or.𝔐.ξ z (hS.choose p q)
      ((Scheme.stalkClosedPointTo z).hom (s p q)) := fun p q =>
    ⟨h, s p q, by rw [hreg, hs], rfl⟩
  have hmat : (Matrix.of fun p q => valAt Dc.y (hS.choose p q) w) =
      Matrix.of fun p q => (Scheme.stalkClosedPointTo z).hom (s p q) := by
    ext p q
    exact valAt_eq hw ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie z w h hco _ _).1 (hval p q))
  rw [gramAt, dite_eq_left hex, dite_eq_left hS, hmat]
  refine (GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z Dc.N (fun k => Or.i τ ((Dc.h τ).b hex.choose k))
    (fun k => Or.i τ (b k)) _ G hS.choose _ (GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hint)
    (Or.metric τ hex.choose z w hco hint hex.choose_spec) hG ?_ hval).symm
  intro q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hS.choose_spec q, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MuFrame

private theorem isMultiHomog_mul_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a b : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hp m1 h1 k, hq m2 h2 k, Pi.add_apply]

private theorem isMultiHomog_add_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

private theorem isMultiHomog_X_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] [DecidableEq K]
    (k : K) (i : Jt k) :
    IsMultiHomog (MvPolynomial.X ⟨k, i⟩ : MvPolynomial ((k : K) × Jt k) ℤ) (Pi.single k 1) := by
  classical
  unfold IsMultiHomog
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · have hk' : k ≠ k' := Ne.symm hk
    simp [Finsupp.single_apply, hk, hk']

private theorem isMultiHomog_prod_X_one {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    (ch : (k : K) → Jt k) :
    IsMultiHomog (∏ k, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog
      (∏ k ∈ s, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isMultiHomog_mul_geometry (isMultiHomog_X_geometry a (ch a)) ih
  have h := key Finset.univ
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem isValueAt_add' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s + s') w (v + v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add_geometry (isMultiHomog_mul_geometry hg hh') ?_,
    isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul_geometry hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, map_add (f := _), hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul, map_add (f := _)]; rw [div_add_div _ _ hw hw']; ring

private theorem isValueAt_mul' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s * s') w (v * v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul_geometry hg hg', isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul]; rw [div_mul_div_comm]

private theorem isValueAt_aeval_segreCoord_div {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {Ω : Type} [Field Ω] (y : (k : K) × Jt k → Ω) (w : (k : K) × Jt k → ℂ) (ch : (k : K) → Jt k)
    (hy : segreCoord y ch ≠ 0) (hw : ∏ k, w ⟨k, ch k⟩ ≠ 0) (P : MvPolynomial ((k : K) → Jt k) ℤ) :
    IsValueAt y (MvPolynomial.aeval (fun c' => segreCoord y c' / segreCoord y ch) P) w
      (MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    unfold IsValueAt
    refine ⟨0, MvPolynomial.C a, 1, isMultiHomog_C_zero a, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · simp
    · simp
    · simp
    · simp
  | add p q hp hq => simpa only [map_add (f := _)] using isValueAt_add' hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine isValueAt_mul' hp ?_
    unfold IsValueAt
    refine ⟨fun _ => 1, ∏ k, MvPolynomial.X ⟨k, i k⟩, ∏ k, MvPolynomial.X ⟨k, ch k⟩,
      isMultiHomog_prod_X_one i, isMultiHomog_prod_X_one ch, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hy
    · simp only [map_prod, MvPolynomial.aeval_X]
      exact (div_mul_cancel₀ _ hy).symm
    · simpa using hw
    · simp [MvPolynomial.aeval_X]

theorem nonempty_muFrameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  classical
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hco
  unfold CoordsAt at hco
  choose ch hch using hco.1
  have hy : ∀ k, Dc.y ⟨k, ch k⟩ ≠ 0 := fun k => (hco.2 k (ch k) (hch k)).1
  have hwc : ∀ k, w ⟨k, ch k⟩ ≠ 0 := fun k => (hch k).ne_zero
  have hseg : segreCoord Dc.y ch ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hy k)
  have hsegw : ∏ k, w ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hwc k)
  obtain ⟨m, f, cc, hf, hcc, hsum, hfr⟩ := Hd.locally ch hseg
  have hmem : ∀ a, a ∈ chartRing ℤ (segreCoord Dc.y) ch → ∃ P : MvPolynomial ((k : K) → J k) ℤ,
      MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) P = a := by
    intro a ha
    unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at ha
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨P, hP⟩ := ha
    exact ⟨P, hP⟩
  choose P hP using fun l => hmem (f l) (hf l)
  choose Q hQ using fun l => hmem (cc l) (hcc l)
  have hginj : Function.Injective (genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩) :=
    (CoordTie.gen Or.𝔐.tie).inj _
  have hlift : ∀ q : (k : K) × J k, ∃ t : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ t = Dc.y q / Dc.y ⟨q.1, ch q.1⟩ ∧
      (Scheme.stalkClosedPointTo z).hom t = w q / w ⟨q.1, ch q.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r0, hv, hr0⟩ := (hco.2 k (ch k) (hch k)).2 i
    unfold ValAt at hv
    obtain ⟨hsp, t, ht1, ht2⟩ := hv
    refine ⟨t, ht1, ?_⟩
    rw [ht2, hr0, mul_div_assoc, div_self (hwc k), _root_.mul_one]
  choose t ht1 ht2 using hlift
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Or.𝔐.X.presheaf.stalk (centre z) →+* ℂ,
      ψ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have ht2' : ∀ q, ψ (t q) = w q / w ⟨q.1, ch q.1⟩ := by
    intro q; rw [hψ]; exact ht2 q
  have hval : ∀ R : MvPolynomial ((k : K) → J k) ℤ, ∃ s : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s =
        MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) R ∧
      ψ s =
        MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      refine ⟨((a : ℤ) : Or.𝔐.X.presheaf.stalk (centre z)), ?_, ?_⟩
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
    | add p q hp hq =>
      obtain ⟨s, hs1, hs2⟩ := hp
      obtain ⟨s', hs1', hs2'⟩ := hq
      exact ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs1, hs1'], by rw [map_add (f := _), map_add (f := _), hs2, hs2']⟩
    | mul_X p i hp =>
      obtain ⟨s, hs1, hs2⟩ := hp
      refine ⟨s * ∏ k, t ⟨k, i k⟩, ?_, ?_⟩
      · rw [map_mul, map_prod, hs1, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht1]
        unfold segreCoord
        rw [Finset.prod_div_distrib]
      · rw [map_mul, map_prod, hs2, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht2']
        rw [Finset.prod_div_distrib]
  obtain ⟨s, hs1, hs2⟩ := hval (∑ l, Q l * P l - 1)
  have hz : genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs1, map_sub, map_sum, map_one]
    simp only [map_mul, hP, hQ]
    rw [hsum, sub_self]
  have hs0 : s = 0 := hginj (by rw [hz, map_zero])
  have hW : ∑ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (Q l) *
      MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) = 1 := by
    have h2 := hs2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs0, map_zero, map_sub, map_sum, map_one] at h2
    simp only [map_mul] at h2
    exact sub_eq_zero.mp h2.symm
  obtain ⟨l0, hl0⟩ : ∃ l, MvPolynomial.aeval
      (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun l _ => by rw [hne l, MulZeroClass.mul_zero])] at hW
    exact zero_ne_one hW
  have hunit : IsUnitAt Dc.y (f l0) w := by
    have hv := isValueAt_aeval_segreCoord_div Dc.y w ch hseg hsegw (P l0)
    rw [hP l0] at hv
    exact Exists.intro _ (And.intro hv hl0)
  obtain ⟨b, hb, u, hu, hΛ⟩ := hfr l0
  exact ⟨MuFrameAt.mk ch (f l0) (And.intro hwc hunit) b hb u hu hΛ⟩

end GlobalTheory.CompanionTheory.Ar.MuFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_hodge_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt | exact GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mem_Vgen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem disjoint_blocks (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem exists_smallPart (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) :
    ∃ s, Or.IsSmallPart d s := by
  have h : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem frames (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt (d.b τ) ⟨centre z, h⟩ ∧
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ ∧
    ∀ k, Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ := by
  have hfr := GlobalTheory.T.component_data_hodge_second E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  have hb := GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (disjoint_blocks Or τ) (fun _ hx => mem_Vgen _ _ _ hx) (fun _ hx => mem_Vgen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)
  exact ⟨hfr, hb.1, hb.2.1⟩

theorem norm_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) :
    ∃ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) ∧ (∀ τ, (Γ τ).PosDef) ∧
      d.norm = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have key : ∀ τ, ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) Γ ∧ Γ.PosDef ∧
        quotNormSq Dc.j_le_N (gramAt (Dc.h τ) (d.b τ) w) = Γ.det.re := fun τ => by
    obtain ⟨h1, h2, h3⟩ := frames Or hw d hs τ h
    obtain ⟨G, hG, hGp⟩ := GlobalTheory.T.component_data_hodge_third E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) h hi h1
    rw [GlobalTheory.T.intersection_system_hodge_data E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ (d.b τ) h G hw hi h1 hG]
    exact GlobalTheory.T.intersection_system_hodge_bound E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) (s τ) h G hi h1
      ((d.adapted τ).2.2) (fun k => (hs τ k).1) h3 h2 hG hGp
  choose Γ h1 h2 h3 using key
  refine ⟨Γ, h1, h2, ?_⟩
  unfold MuFrameAt.norm
  simp_rw [h3]

theorem det_re_pos {n : ℕ} {Γ : Matrix (Fin n) (Fin n) ℂ} (h : Γ.PosDef) : 0 < Γ.det.re :=
  (Complex.pos_iff.1 h.det_pos).1

theorem phMu_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ}
    (hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      (∑ τ, Real.log (Γ τ).det.re) / 2 := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  haveI : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  obtain ⟨cv, hcv, hwc⟩ := exists_eq_smul_orbitRep w
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = orbitRep w := ⟨_, rfl⟩
  rw [← hw₀def] at hwc
  have hwk : ∀ p, w p = cv p.1 * w₀ p := fun p => congrFun hwc p
  have hw₀ : CoordsAt Or.𝔐.ξ Dc.y z w₀ := by
    have := RootHt.ArchB.coordsAt_smul (fun k => (cv k)⁻¹) (fun k => inv_ne_zero (hcv k)) hw
    convert this using 1
    funext p
    rw [hwc]
    simp [torusSmul, inv_mul_cancel_left₀ (hcv p.1)]
  have hval : ∀ (a : Ω) (v : ℂ), IsValueAt Dc.y a w v ↔ IsValueAt Dc.y a w₀ v := fun a v =>
    ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw a v).symm).trans
      (GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w₀ h hw₀ a v)
  have hne₀ : ∀ k, w₀ ⟨k, d.c k⟩ ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hwk ⟨k, d.c k⟩]; simp [h0])
  let d₁ : MuFrameAt Hd w₀ :=
    { c := d.c, f := d.f
      inDom := ⟨hne₀, d.inDom.2.imp fun v hv => ⟨(hval _ _).1 hv.1, hv.2⟩⟩
      b := d.b, adapted := d.adapted, u := d.u, unit := d.unit, eq := d.eq }
  have hs₁ : Or.IsSmallPart d₁ s := hs
  have hu := GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hmc₀ : w₀ ∈ mcPts (mCoordIdeal Dc.y) :=
    (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w₀).2 ⟨z, h, hw₀⟩
  have hu₀ : valAt Dc.y d.u w₀ = valAt Dc.y d.u w :=
    valAt_eq hmc₀ ((hval _ _).1 ((GlobalTheory.T.valAt_iff_value_at Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).1 hu.2))

  have hne := GlobalTheory.T.component_data_hodge_first E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hw₀
  obtain ⟨s₀, hs₀⟩ := exists_smallPart Or hne.some
  obtain ⟨Γ₀, g₀, p₀, n₀⟩ := norm_eq Or hw₀ hi hne.some hs₀
  obtain ⟨Γ₁, g₁, p₁, -⟩ := norm_eq Or hw₀ hi d₁ hs₁
  have e₁ : Γ₁ = Γ := funext fun τ =>
    GlobalTheory.T.gram_matrix_change_frame E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) _ _ hpol (g₁ τ) (hΓ τ)
  subst e₁
  have hind := GlobalTheory.T.intersection_system_hodge_degree E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hne.some d₁ s₀ s Γ₀ Γ₁ hw₀ hi hs₀ hs₁ g₀ g₁ p₀
  have hF : muMetric Hd w₀ = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    unfold muMetric
    rw [dite_eq_left hne, n₀, hind]
    show ‖valAt Dc.y d.u w₀‖ * _ * _ = _
    rw [hu₀]
  have hA : 0 < ‖valAt Dc.y d.u w‖ := norm_pos_iff.2 hu.1
  have hsq : 0 < ∏ τ, Real.sqrt (Γ₁ τ).det.re :=
    Finset.prod_pos fun τ _ => Real.sqrt_pos.2 (det_re_pos (p₁ τ))
  have hprod₀ : 0 < ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hne₀ k)) _
  have hprod : 0 < ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  have hpos : 0 < muMetric Hd w₀ := by
    rw [hF]
    positivity
  have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨d.c k, d.inDom.1 k⟩
  have hh : (muLine Hd).h w = (∏ k, ‖cv k‖ ^ Hd.aMu k) * muMetric Hd w₀ := by
    subst hw₀def
    exact TopNPoly.hermOfFun_h_smul hcv hwc hnz hpos
  have hcw : (∏ k, ‖cv k‖ ^ Hd.aMu k) * ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k = ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul]
    rw [hwk ⟨k, d.c k⟩]
  have hfin : (muLine Hd).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    rw [hh, hF, ← hcw]
    ring
  show Real.log ((muLine Hd).h w) = _
  rw [hfin, Real.log_mul (by positivity) hsq.ne', Real.log_prod (fun τ _ => (Real.sqrt_pos.2 (det_re_pos (p₁ τ))).ne')]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (det_re_pos (p₁ τ)).le

theorem phMu_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro _ E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hw
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  refine ⟨GlobalTheory.T.component_data_hodge_first E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw, fun d => ⟨exists_smallPart Or d, fun s hs => ⟨
    fun τ h => (frames Or hw d hs τ h).2.1, ?_, fun hi Γ hΓ => phMu_eq Or hw hi d hs hΓ⟩⟩⟩
  exact (GlobalTheory.T.unit_value_frame_domain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie (Or.𝔐.all _) hw d.inDom d.unit).1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_intersection_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small | exact GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small <;> assumption)
end

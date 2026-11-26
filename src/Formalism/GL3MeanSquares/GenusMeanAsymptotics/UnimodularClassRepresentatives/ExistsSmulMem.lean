module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
public import Lemmata.GeneralBFactSecondForm.Imports
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LinearIndependentOfGramDetNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanSInduction

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardStabilizerAutSub
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · refine { toIsLattice := ?_, span_eq_top := ?_ }
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.IsLattice.of_fg K (hLat.fg.map _)
    · change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact g.surjective
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := hd x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

theorem exists_smul_mem {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) (v : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • v ∈ Λ :=
  Bl.general_b_fact_second_form.goal1 hΛ v

scoped instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem smul_pair (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, g.1 p.2) := rfl

def stabLatEquiv (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) Λ ≃ Formalism.ThetaLiftIndependence.autL h Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (n : K) :
    Set (Submodule (𝓞 K) V × V) :=
  {p | p.1 ∈ Formalism.HermitianLatticesTheory.genus h L ∧ p.2 ∈ p.1 ∧ h p.2 p.2 = n}

theorem apply_mem_gmap (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Λ) :
    g x ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
  exact hx

theorem pairs_stable (hs : h.IsSymm) (L : Submodule (𝓞 K) V) (n : K) (g : Formalism.HermitianLatticesTheory.isom h)
    (p : Submodule (𝓞 K) V × V) (hp : p ∈ pairs h L n) : g • p ∈ pairs h L n :=
  ⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩

def perpO (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) : Submodule (𝓞 K) V :=
  (LinearMap.ker (h x)).restrictScalars (𝓞 K)

theorem mem_perpO (x v : V) : v ∈ perpO h x ↔ h x v = 0 := Iff.rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Submodule (𝓞 K) V × V) : Submodule (𝓞 K) V × V :=
  (p.1 ⊓ perpO h p.2, p.2)

theorem proj_smul (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    proj h (g • p) = g • proj h p := by
  refine Prod.ext ?_ rfl
  ext v
  change v ∈ Formalism.HermitianLatticesTheory.gmap g.1 p.1 ⊓ perpO h (g.1 p.2) ↔
    v ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p.1 ⊓ perpO h p.2)
  rw [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.mem_inf,
    mem_perpO, mem_perpO]
  have : h (g.1 p.2) v = h p.2 (g.1.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply g.1 v]
    exact g.2 _ _
  rw [this]

end One

section Two

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux

theorem isLattice_cut (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) : Submodule.IsLattice K (S.cut Λ) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    have hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj
      (Submodule.FG.of_le_of_isNoetherian hle)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem isFullLattice_cut (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) : Submodule.IsFullLattice K (S.cut L) := by
  refine { toIsLattice := isLattice_cut S hL.toIsLattice, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro a _
  have ha : S.ι a ∈ Submodule.span K (L : Set V) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, r, hya⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).mp ha
  rw [Submodule.span_eq] at hy
  have hr : (r : 𝓞 K) • a ∈ S.cut L := by
    rw [S.mem_cut_iff, ← algebraMap_smul K (r : 𝓞 K), map_smul, hya, smul_smul,
      IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  have hmul := Submodule.smul_mem (Submodule.span K (S.cut L : Set V'))
    (IsLocalization.mk' K 1 r) (Submodule.subset_span hr)
  rwa [← algebraMap_smul K (r : 𝓞 K), smul_smul, IsLocalization.mk'_spec, map_one, one_smul] at hmul

def emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Λ'.map (S.ι.restrictScalars (𝓞 K))

theorem cut_emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : S.cut (emb S Λ') = Λ' :=
  Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'

theorem emb_injective (S : VecSplit h h') : Function.Injective (emb S) := fun A B e => by
  rw [← cut_emb S A, e, cut_emb]

theorem inf_perpO (S : VecSplit h h') (Λ : Submodule (𝓞 K) V) :
    Λ ⊓ perpO h S.x₀ = emb S (S.cut Λ) := by
  ext v
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨a, rfl⟩ := exists_of_orth S hv0
    exact Submodule.mem_map.mpr ⟨a, hv, rfl⟩
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨ha, S.orth a⟩

theorem gmap_extOf_emb (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (C : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (emb S C) = emb S (Formalism.HermitianLatticesTheory.gmap g' C) := by
  unfold Formalism.HermitianLatticesTheory.gmap emb
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext a
  exact extOf_ι S g' a

theorem cut_gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (Λ : Submodule (𝓞 K) V) :
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap g' (S.cut Λ) := by
  ext a
  rw [VecSplit.mem_cut_iff, mem_gmap_iff, mem_gmap_iff, VecSplit.mem_cut_iff, eq_decomp_ι S a,
    extOf_symm_apply, ← eq_decomp_ι]

theorem stab_pair_iff (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') (g : Formalism.HermitianLatticesTheory.isom h) :
    g ∈ MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ↔
      Formalism.HermitianLatticesTheory.gmap g.1 (emb S Λ') = emb S Λ' ∧ g.1 S.x₀ = S.x₀ := by
  rw [MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]

def stabPairEquiv (hs : h.IsSymm) (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ≃
      Formalism.ThetaLiftIndependence.autL h' Λ' where
  toFun a := ⟨res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2,
    res_mem_isom S _ _ _, by
      have := gmap_res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2
        ((stab_pair_iff S Λ' a.1).mp a.2).1
      rwa [cut_emb] at this⟩
  invFun b := ⟨⟨extOf S b.1, extOf_mem_isom hs S b.2.1⟩, (stab_pair_iff S Λ' _).mpr
    ⟨by rw [gmap_extOf_emb, b.2.2], extOf_x₀ S _⟩⟩
  left_inv a := Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
    (linearMap_ext S (by simp [extOf_x₀, ((stab_pair_iff S Λ' a.1).mp a.2).2])
      (fun v => by simp [extOf_ι, res_spec]))))
  right_inv b := Subtype.ext (LinearEquiv.ext fun v => S.inj (by simp [res_spec, extOf_ι]))

end Two

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem aniso_of_totPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x, h x x = 0 → x = 0 := by
  intro x hx
  by_contra hne
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hd x hne φ
  rw [hx, map_zero] at this
  simp at this

theorem exists_gram {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {n : ℕ} (x : Fin n → V) (hx : ∀ i, x i ∈ L) :
    ∃ g : Matrix (Fin n) (Fin n) (𝓞 K), (∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) ∧
      algebraMap (𝓞 K) K g.det = (Matrix.of fun i j => h (x i) (x j)).det := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (x i) (hx i) (x j) (hx j))
  refine ⟨Matrix.of g, hg, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hg i j

theorem discrIdeal_ne_bot [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : discrIdeal h L ≠ ⊥ := by
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (finBasis K V i)
  have hli : LinearIndependent K (fun i => n i • finBasis K V i) := by
    have h1 := (finBasis K V).linearIndependent.units_smul
      (fun i => Units.mk0 (n i : K) (by exact_mod_cast hn i))
    convert h1 using 1
    funext i
    rw [Pi.smul_apply', Units.smul_def, Units.val_mk0, Int.cast_smul_eq_zsmul]
  obtain ⟨g, -, hdet⟩ := exists_gram hLi _ hnx
  intro hbot
  have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hnx, hdet⟩
  rw [hbot, Ideal.mem_bot] at hmem
  apply gram_det_ne_zero h hd _ hli
  rw [← hdet, hmem, map_zero]

theorem vd_eq_zero_of_not_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hn : ¬ discrIdeal h L ≤ extP K 𝔭) : vd h L 𝔭 = 0 := by
  unfold vd
  have h1 : {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} = {0} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hn (he.trans (Ideal.pow_le_self h0))
    · rintro rfl
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  rw [h1, csSup_singleton]

theorem not_le_of_vd_eq_zero {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hD : discrIdeal h L ≠ ⊥) (hE : extP K 𝔭 ≠ ⊤) (h0 : vd h L 𝔭 = 0) :
    ¬ discrIdeal h L ≤ extP K 𝔭 := by
  intro hle
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have h1 : 1 ≤ vd h L 𝔭 := le_csSup hb (by simpa using hle)
  omega

end Formalism.HermitianLattices.Ext.L3.LocF
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTuple
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gram (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (x : Fin n → V) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => h (x i) (x j)

def spanS (S : Subring K) {n : ℕ} (x : Fin n → V) : Submodule S V :=
  Submodule.span S (Set.range x)

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem mem_spanS {n : ℕ} (x : Fin n → V) (i : Fin n) : x i ∈ spanS S x :=
  Submodule.subset_span ⟨i, rfl⟩

theorem smul_mem_spanS {n : ℕ} {x : Fin n → V} {c : K} (hc : c ∈ S) {v : V} (hv : v ∈ spanS S x) :
    c • v ∈ spanS S x :=
  (spanS S x).smul_mem (⟨c, hc⟩ : S) hv

theorem spanS_induction {n : ℕ} {x : Fin n → V} {p : V → Prop} (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ c ∈ S, ∀ a, p a → p (c • a))
    (hx : ∀ i, p (x i)) : ∀ v ∈ spanS S x, p v := by
  first | exact UpperTheory.Reformulated.B.Qe24.spanS_induction .. | (apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe24.spanS_induction <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p h0 | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x p | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n x | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S n | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› S | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V ‹_› | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K V | exact @UpperTheory.Reformulated.B.Qe24.spanS_induction K

theorem int_spanS (hS : IsHermSemilocal S) {n : ℕ} {x : Fin n → V}
    (hx : ∀ i j, h (x i) (x j) ∈ S) : ∀ a ∈ spanS S x, ∀ b ∈ spanS S x, h a b ∈ S := by
  intro a ha
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add (f := _)]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smul]; exact S.mul_mem hc hb) (fun j => ?_)
  revert a
  refine spanS_induction (by simp [S.zero_mem]) (fun b c hb hc => by
    rw [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hb hc) (fun c hc b hb => by
    rw [map_smulₛₗ, LinearMap.smul_apply]; exact S.mul_mem (hS.star_mem _ hc) hb)
    (fun i => hx i j)

theorem exists_coeff {n : ℕ} {y : Fin n → V} {v : V} (hv : v ∈ spanS S y) :
    ∃ c : Fin n → S, v = ∑ j, (c j : K) • y j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hv
  exact ⟨c, hc.symm⟩

theorem gram_det_of_le (hS : IsHermSemilocal S) {n : ℕ} {x y : Fin n → V}
    (hxy : ∀ i, x i ∈ spanS S y) : ∃ c ∈ S, (gram h x).det = c * (gram h y).det := by
  choose T hT using fun i => exists_coeff (hxy i)
  have e : gram h x = ((S.subtype.mapMatrix (Matrix.of T)).map star) * gram h y *
      (S.subtype.mapMatrix (Matrix.of T)).transpose := by
    ext i l
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Subring.subtype_apply]
    conv_lhs => rw [hT i, hT l]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ((S.subtype.mapMatrix (Matrix.of T)).map star).det =
      star (S.subtype.mapMatrix (Matrix.of T)).det := by
    have := (starRingEnd K).map_det (S.subtype.mapMatrix (Matrix.of T))
    rw [starRingEnd_apply] at this
    rw [this]
    rfl
  have e3 : (S.subtype.mapMatrix (Matrix.of T)).det ∈ S := by
    rw [← RingHom.map_det]
    exact (Matrix.of T).det.2
  refine ⟨star (S.subtype.mapMatrix (Matrix.of T)).det * (S.subtype.mapMatrix (Matrix.of T)).det,
    S.mul_mem (hS.star_mem _ e3) e3, ?_⟩
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2]
  ring

theorem gram_det_cons (hs : h.IsSymm) {n : ℕ} (f : V) (x : Fin n → V) (hf : ∀ k, h f (x k) = 0) :
    (gram h (Fin.cons f x : Fin (n + 1) → V)).det = h f f * (gram h x).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin n, (-1 : K) ^ (i.succ : ℕ) * gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 *
      ((gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix i.succ.succAbove Fin.succ).det = 0 := by
    intro i
    have : gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 = 0 := by
      simp only [gram, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
      rw [← show star (h f (x i)) = h (x i) f from hs.eq f (x i), hf, star_zero]
    rw [this]
    ring
  rw [Finset.sum_eq_zero fun i _ => h1 i, add_zero]
  have h2 : (gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix (Fin.succAbove 0) Fin.succ =
      gram h x := by
    ext i j
    simp [gram]
  rw [h2]
  simp [gram]

theorem gram_det_dv (hπ : IsUnif S π) {n : ℕ} (x : Fin (n + 2) → V)
    (hx : ∀ i j, Dv S π (h (x i) (x j))) : Dv S π ((gram h x).det * π⁻¹) := by
  have e : gram h x = π • S.subtype.mapMatrix
      (Matrix.of fun i j => (⟨h (x i) (x j) * π⁻¹, hx i j⟩ : S)) := by
    ext i j
    have := hπ.ne
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Subring.subtype_apply, smul_eq_mul]
    field_simp
  rw [e, Matrix.det_smul, ← RingHom.map_det, Fintype.card_fin]
  unfold Dv
  have e2 : ∀ d : K, π ^ (n + 2) * d * π⁻¹ * π⁻¹ = π ^ n * d := by
    intro d
    have := hπ.ne
    field_simp
    ring
  rw [e2]
  exact S.mul_mem (S.pow_mem hπ.mem n) (Subtype.mem _)

theorem exists_pivot (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {n : ℕ}
    (x : Fin (n + 1) → V) (hx : ∀ i j, h (x i) (x j) ∈ S)
    (hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))) :
    ∃ i₀ : Fin (n + 1), ∃ r ∈ spanS S (x ∘ i₀.succAbove), IsUnitIn S (h (x i₀ + r) (x i₀ + r)) := by
  obtain ⟨i, j, hij⟩ := hnd
  by_cases h1 : IsUnitIn S (h (x i) (x i))
  · exact ⟨i, 0, Submodule.zero_mem _, by simpa using h1⟩
  by_cases h2 : IsUnitIn S (h (x j) (x j))
  · exact ⟨j, 0, Submodule.zero_mem _, by simpa using h2⟩
  have d1 := dv_of_not_unit hπ (hx i i) (hs.eq _ _) h1
  have d2 := dv_of_not_unit hπ (hx j j) (hs.eq _ _) h2
  have hne : j ≠ i := by
    rintro rfl
    exact hij d1
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hx i j) hij S.one_mem (star_one K)
  refine ⟨i, s • x j, smul_mem_spanS hsS (by rw [← hk]; exact mem_spanS (x ∘ i.succAbove) k), ?_⟩
  have hji : h (x j) (x i) = star (h (x i) (x j)) := (hs.eq _ _).symm
  have e : h (x i + s • x j) (x i + s • x j) =
      1 + (star s * s * h (x j) (x j) + h (x i) (x i)) := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hji,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d2.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d1)

theorem spanS_cons {n : ℕ} (f : V) (y : Fin n → V) :
    spanS S (Fin.cons f y : Fin (n + 1) → V) = Submodule.span S {f} ⊔ spanS S y := by
  unfold spanS
  rw [Fin.range_cons, Submodule.span_insert]

theorem exists_orth_tuple (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) :
    ∀ (n : ℕ) (x : Fin n → V), (∀ i j, h (x i) (x j) ∈ S) →
      ¬ Dv S π ((gram h x).det * π⁻¹) →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by
  intro n
  induction n with
  | zero => exact fun x _ _ => ⟨x, fun i => i.elim0, rfl⟩
  | succ n ih =>
    intro x hx hdet
    by_cases hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))
    · obtain ⟨i₀, r, hr, hu⟩ := exists_pivot hS hπ hs x hx hnd
      have hrx : r ∈ spanS S x :=
        Submodule.span_mono (Set.range_comp_subset_range _ _) hr
      have hint := int_spanS hS hx
      generalize hfdef : x i₀ + r = f at hu
      have hf : f ∈ spanS S x := by
        rw [← hfdef]; exact (spanS S x).add_mem (mem_spanS x i₀) hrx
      have hc : ∀ k, h f (x (i₀.succAbove k)) * (h f f)⁻¹ ∈ S := fun k =>
        S.mul_mem (hint f hf _ (mem_spanS x _)) hu.2.2
      let x' : Fin n → V := fun k =>
        x (i₀.succAbove k) - (h f (x (i₀.succAbove k)) * (h f f)⁻¹) • f
      have hx'mem : ∀ k, x' k ∈ spanS S x := fun k =>
        (spanS S x).sub_mem (mem_spanS x _) (smul_mem_spanS (hc k) hf)
      have hfx' : ∀ k, h f (x' k) = 0 := by
        intro k
        have := hu.1
        simp only [x', map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      have hf0 : f ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
        mem_spanS (Fin.cons f x' : Fin (n + 1) → V) 0
      have hge1 : ∀ k, x (i₀.succAbove k) ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro k
        have h1 : x' k ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) :=
          mem_spanS (Fin.cons f x' : Fin (n + 1) → V) k.succ
        have h2 := Submodule.add_mem _ h1 (smul_mem_spanS (hc k) hf0)
        simpa only [x', sub_add_cancel] using h2
      have hge : ∀ i, x i ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
        intro i
        rcases Fin.eq_self_or_eq_succAbove i₀ i with rfl | ⟨k, rfl⟩
        · have h1 : r ∈ spanS S (Fin.cons f x' : Fin (n + 1) → V) := by
            refine (Submodule.span_le.mpr ?_) hr
            rintro _ ⟨k, rfl⟩
            exact hge1 k
          have h2 := Submodule.sub_mem _ hf0 h1
          have e : f - r = x i := by rw [← hfdef, add_sub_cancel_right]
          rwa [e] at h2
        · exact hge1 k
      have hspan : spanS S (Fin.cons f x' : Fin (n + 1) → V) = spanS S x := by
        apply le_antisymm
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          refine Fin.cases ?_ (fun k => ?_) i
          · exact hf
          · exact hx'mem k
        · refine Submodule.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          exact hge i
      obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS hge
      rw [gram_det_cons hs f x' hfx'] at hcdet
      obtain ⟨y', horth, hspan'⟩ := ih x' (fun i j => hint _ (hx'mem i) _ (hx'mem j)) (by
        intro hd
        apply hdet
        have e : (gram h x).det * π⁻¹ = c * h f f * ((gram h x').det * π⁻¹) := by
          rw [hcdet]; ring
        rw [e]
        exact hd.mul_left (S.mul_mem hcS hu.2.1))
      have hfy : ∀ k, h f (y' k) = 0 := by
        intro k
        have h1 : y' k ∈ spanS S x' := by rw [← hspan']; exact mem_spanS y' k
        exact spanS_induction (p := fun v => h f v = 0) (by simp)
          (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
          (fun c _ a ha => by rw [map_smul, ha, smul_zero]) hfx' _ h1
      refine ⟨Fin.cons f y', ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
        · intro hne; exact absurd rfl hne
        · intro _; simpa using hfy l
        · intro _
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [← show star (h f (y' k)) = h (y' k) f from hs.eq _ _, hfy, star_zero]
        · intro hne
          simp only [Fin.cons_succ]
          exact horth k l fun hkl => hne (by rw [hkl])
      · rw [← hspan, spanS_cons, spanS_cons, hspan']
    · push Not at hnd
      cases n with
      | zero => exact ⟨x, fun i j hij => absurd (by omega : i = j) hij, rfl⟩
      | succ m => exact absurd (gram_det_dv hπ x hnd) hdet

end Formalism.HermitianLattices.Ext.L3.U0
end
end

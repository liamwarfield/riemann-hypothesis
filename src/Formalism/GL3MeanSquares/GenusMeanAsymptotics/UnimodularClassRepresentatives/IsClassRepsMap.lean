module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, IsClassReps h L s := ⟨s, hs⟩
  rw [massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs

section Transfer

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsFullLattice K (Φ M) ↔ Submodule.IsFullLattice K M)

include hτ hg hloc hlat

theorem mem_genus_iff (L M : Submodule (𝓞 K) V) : Φ M ∈ genus h' (Φ L) ↔ M ∈ genus h L := by
  unfold genus SameGenus
  simp only [Set.mem_ofPred_eq, hlat]
  refine and_congr_right fun _ => forall₂_congr fun p hp => ?_
  constructor
  · rintro ⟨g', hg', e⟩
    obtain ⟨g, rfl⟩ := τ.surjective g'
    refine ⟨g, (hτ g).1 hg', Φ.injective ?_⟩
    rw [hg, hloc p hp, hloc p hp, e]
  · rintro ⟨g, hg₁, e⟩
    refine ⟨τ g, (hτ g).2 hg₁, ?_⟩
    rw [← hloc p hp, ← hg, e, hloc p hp]

theorem isClassReps_map {L : Submodule (𝓞 K) V} {s : Finset (Submodule (𝓞 K) V)}
    (hs : IsClassReps h L s) : IsClassReps h' (Φ L) (s.map Φ.toEmbedding) := by
  constructor
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_map.1 hN
    exact (mem_genus_iff Φ τ hτ hg hloc hlat L M).2 (hs.1 M hM)
  · intro N hN
    obtain ⟨M, rfl⟩ := Φ.surjective N
    obtain ⟨M₀, ⟨hM₀, g, hg₀, e⟩, huniq⟩ := hs.2 M ((mem_genus_iff Φ τ hτ hg hloc hlat L M).1 hN)
    refine ⟨Φ M₀, ⟨Finset.mem_map.2 ⟨M₀, hM₀, rfl⟩, τ g, (hτ g).2 hg₀, by rw [← hg, e]⟩, ?_⟩
    rintro N₁ ⟨hN₁, g', hg', e'⟩
    obtain ⟨M₁, hM₁, rfl⟩ := Finset.mem_map.1 hN₁
    obtain ⟨g₁, rfl⟩ := τ.surjective g'
    have : M₁ = M₀ := huniq M₁ ⟨hM₁, g₁, (hτ g₁).1 hg', Φ.injective (by rw [hg]; exact e')⟩
    rw [this]; rfl

theorem card_autL_eq (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (Φ M)) = Nat.card (autL h M) := by
  refine (Nat.card_congr (τ.subtypeEquiv fun g => ?_)).symm
  change (g ∈ isom h ∧ gmap g M = M) ↔ (τ g ∈ isom h' ∧ gmap (τ g) (Φ M) = Φ M)
  rw [hτ, ← hg, Φ.injective.eq_iff]

theorem mass_transfer {L : Submodule (𝓞 K) V} (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (Φ L) s') ∧ mass h' (Φ L) = mass h L := by
  obtain ⟨s, hs⟩ := hex
  have hs' := isClassReps_map Φ τ hτ hg hloc hlat hs
  refine ⟨⟨_, hs'⟩, ?_⟩
  rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ hs', Finset.sum_map]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Equiv.coe_toEmbedding, card_autL_eq Φ τ hτ hg hloc hlat M]

end Transfer

def mapE (φ : V ≃ₗ[K] V') : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V' :=
  (Submodule.orderIsoMapComap (φ.restrictScalars (𝓞 K))).toEquiv

theorem mem_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') :
    y ∈ mapE φ M ↔ φ.symm y ∈ M := by
  change y ∈ M.map ((φ.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V') ↔ _
  rw [Submodule.mem_map_equiv]; rfl

def conjE (φ : V ≃ₗ[K] V') : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V') where
  toFun g := (φ.symm.trans g).trans φ
  invFun g := (φ.trans g).trans φ.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp

theorem conjE_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    conjE φ g y = φ (g (φ.symm y)) := rfl

theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ gmap g M ↔ g.symm y ∈ M := by
  change y ∈ M.map ((g.restrictScalars (𝓞 K)) : V →ₗ[𝓞 K] V) ↔ _
  rw [Submodule.mem_map_equiv]; rfl

theorem isLattice_mapE (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (mapE φ M) := by
  constructor
  · exact hM.fg.map _
  · exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

theorem isFullLattice_mapE (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (mapE φ M) := by
  refine { toIsLattice := isLattice_mapE φ hM.toIsLattice, span_eq_top := ?_ }
  change Submodule.span K ((φ : V →ₗ[K] V') '' (M : Set V)) = ⊤
  rw [Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact φ.surjective

theorem mapE_symm_mapE (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : mapE φ.symm (mapE φ M) = M := by
  ext x; simp [mem_mapE]

theorem mass_mapE (φ : V ≃ₗ[K] V') {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (mapE φ L) s') ∧ mass h' (mapE φ L) = mass h L := by
  refine mass_transfer (mapE φ) (conjE φ) ?_ ?_ ?_ ?_ hex
  · intro g
    constructor
    · intro H x y
      have := H (φ x) (φ y)
      simpa [conjE_apply, hφ] using this
    · intro H x y
      obtain ⟨x, rfl⟩ := φ.surjective x
      obtain ⟨y, rfl⟩ := φ.surjective y
      simp only [conjE_apply, LinearEquiv.symm_apply_apply, hφ]
      exact H x y
  · intro g M
    ext y
    rw [mem_mapE, mem_gmap, mem_gmap, mem_mapE]
    have e : (conjE φ g).symm y = φ (g.symm (φ.symm y)) := rfl
    rw [e, LinearEquiv.symm_apply_apply]
  · intro p _ M
    ext y
    rw [mem_mapE]
    change (∃ s ∈ hcompl (K := K) p, s • φ.symm y ∈ M) ↔ (∃ s ∈ hcompl (K := K) p, s • y ∈ mapE φ M)
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [mem_mapE]
    have : φ.symm (s • y) = s • φ.symm y := (φ.symm.restrictScalars (𝓞 K)).map_smul s y
    rw [this]
  · intro M
    refine ⟨fun H => ?_, isFullLattice_mapE φ⟩
    have := isFullLattice_mapE φ.symm H
    rwa [mapE_symm_mapE] at this

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

section Gram

variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]

theorem gram_det_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V) (u w : ι → V) :
    (Matrix.of fun i j => h (u i) (w j)).det =
      star (b.det u) * (Matrix.of fun i j => h (b i) (b j)).det * b.det w := by
  have hm : (Matrix.of fun i j => h (u i) (w j)) =
      (b.toMatrix u).conjTranspose * (Matrix.of fun i j => h (b i) (b j)) * b.toMatrix w := by
    ext i j
    rw [Matrix.of_apply]
    conv_lhs => rw [← b.sum_repr (u i), ← b.sum_repr (w j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Basis.toMatrix_apply, Matrix.of_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply,
    Basis.det_apply]

end Gram

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def gdet (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis (Fin (finrank K V)) K V) : K :=
  (Matrix.of fun i j => h (b i) (b j)).det

theorem mem_discrIdeal {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V} (hx : ∀ i, x i ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x) : z ∈ discrIdeal h L :=
  Ideal.subset_span ⟨x, hx, by rw [hz, gram_det_eq h b]; rfl⟩

theorem discrIdeal_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {I : Ideal (𝓞 K)}
    (hI : ∀ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) → ∀ z : 𝓞 K,
      algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x → z ∈ I) : discrIdeal h L ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro z ⟨x, hx, hz⟩
  exact hI x hx z (by rw [hz, gram_det_eq h b]; rfl)

theorem exists_mixed {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {u w : Fin (finrank K V) → V} (hu : ∀ i, u i ∈ L) (hw : ∀ i, w i ∈ L) :
    ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = star (b.det u) * gdet h b * b.det w := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (u i) (hu i) (w j) (hw j))
  refine ⟨(Matrix.of g).det, ?_⟩
  rw [RingHom.map_det, gdet, ← gram_det_eq h b]
  congr 1
  ext i j
  exact hg i j

theorem update_mem {L : Submodule (𝓞 K) V} {n : ℕ} {x : Fin n → V} {i : Fin n}
    (hx : ∀ k, k ≠ i → x k ∈ L) {y : V} (hy : y ∈ L) : ∀ k, Function.update x i y k ∈ L := by
  intro k
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]; exact hx k hk

theorem algebraMap_conjO (x : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x) := rfl

theorem mem_of_unram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {I : Ideal (𝓞 K)} {z : 𝓞 K}
    (hz : ∀ θ : 𝓞 K, (θ - conjO K θ) * z ∈ I) : z ∈ I := by
  by_contra hn
  let J : Ideal (𝓞 K) :=
    { carrier := {c | c * z ∈ I}
      add_mem' := fun {a c} ha hc => by
        change (a + c) * z ∈ I
        rw [add_mul]; exact I.add_mem ha hc
      zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
      smul_mem' := fun c a ha => by
        change (c • a) * z ∈ I
        rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha }
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 K) * z ∈ I := h1
    rw [one_mul] at h2
    exact hn h2
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  exact hθ (hJP (hz θ))

theorem mixed_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {x : Fin (finrank K V) → V} {i : Fin (finrank K V)} (hx : ∀ k, k ≠ i → x k ∈ L) {y y' : V}
    (hy : y ∈ L) (hy' : y' ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det (Function.update x i y)) * gdet h b *
      b.det (Function.update x i y')) : z ∈ discrIdeal h L := by
  have hu := update_mem hx hy
  have hu' := update_mem hx hy'
  obtain ⟨z11, h11⟩ := exists_mixed hLi b hu hu
  obtain ⟨z22, h22⟩ := exists_mixed hLi b hu' hu'
  obtain ⟨z21, h21⟩ := exists_mixed hLi b hu' hu
  have m11 := mem_discrIdeal b hu h11
  have m22 := mem_discrIdeal b hu' h22
  have key : ∀ θ : 𝓞 K, θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
    intro θ
    have hd : b.det (Function.update x i (y + θ • y')) =
        b.det (Function.update x i y) + algebraMap (𝓞 K) K θ * b.det (Function.update x i y') := by
      rw [← algebraMap_smul K θ y', AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        smul_eq_mul]
    have hw : z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
      refine mem_discrIdeal b (update_mem hx (L.add_mem hy (L.smul_mem θ hy'))) ?_
      rw [hd]
      simp only [map_add (f := _), map_mul, h11, h22, h21, hz, algebraMap_conjO, star_add, star_mul']
      ring
    have he : θ * z + conjO K θ * z21 =
        (z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21) - z11 - conjO K θ * θ * z22 := by
      ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hw m11) (Ideal.mul_mem_left _ _ m22)
  refine mem_of_unram hK fun θ => ?_
  have h1 := key 1
  rw [map_one, one_mul, one_mul] at h1
  have he : (θ - conjO K θ) * z = (θ * z + conjO K θ * z21) - conjO K θ * (z + z21) := by ring
  rw [he]
  exact Ideal.sub_mem _ (key θ) (Ideal.mul_mem_left _ _ h1)


omit [StarRing K] in
theorem exists_prim {J : Type*} [Finite J] (a : J → K) {j₀ : J} (ha : a j₀ ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ≠ ⊤) :
    ∃ (t : K) (c : J → 𝓞 K), (∀ j, algebraMap (𝓞 K) K (c j) = t * a j) ∧ ∃ j, c j ∉ P := by
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) a
  choose e he using hN
  have hN0 : algebraMap (𝓞 K) K (N : 𝓞 K) ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero N
  have he' : ∀ j, algebraMap (𝓞 K) K (e j) = algebraMap (𝓞 K) K (N : 𝓞 K) * a j := by
    intro j
    rw [he j, Algebra.smul_def]
  have hβ : e j₀ ≠ 0 := by
    intro h0
    have := he' j₀
    rw [h0, map_zero] at this
    exact (mul_ne_zero hN0 ha) this.symm
  have hβK : algebraMap (𝓞 K) K (e j₀) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨C, hC⟩ : Ideal.span (Set.range e) ∣ Ideal.span {e j₀} :=
    Ideal.dvd_iff_le.2 (Ideal.span_le.2 (by
      rintro _ rfl
      exact Ideal.subset_span ⟨j₀, rfl⟩))
  have hex : ∃ γ ∈ C, ∃ j, γ * e j ∉ P * Ideal.span {e j₀} := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span {e j₀} ≤ P * Ideal.span {e j₀} := by
      conv_lhs => rw [hC]
      rw [mul_comm, Ideal.mul_le]
      intro γ hγ r hr
      induction hr using Submodule.span_induction with
      | mem r hr => obtain ⟨j, rfl⟩ := hr; exact hcon γ hγ j
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add r s _ _ hr hs => rw [mul_add]; exact Ideal.add_mem _ hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hr
    have heq : P * Ideal.span {e j₀} = 1 * Ideal.span {e j₀} := by
      rw [one_mul]; exact le_antisymm Ideal.mul_le_right hle
    have hs0 : Ideal.span {e j₀} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ
    exact hP (by rw [mul_right_cancel₀ hs0 heq, Ideal.one_eq_top])
  obtain ⟨γ, hγ, j₁, hj₁⟩ := hex
  have hmem : ∀ j, γ * e j ∈ Ideal.span {e j₀} := by
    intro j
    rw [hC, mul_comm γ]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hγ
  choose c hc using fun j => Ideal.mem_span_singleton'.1 (hmem j)
  refine ⟨algebraMap (𝓞 K) K γ * algebraMap (𝓞 K) K (N : 𝓞 K) / algebraMap (𝓞 K) K (e j₀), c,
    fun j => ?_, j₁, fun hcP => hj₁ ?_⟩
  · have := congrArg (algebraMap (𝓞 K) K) (hc j)
    rw [map_mul, map_mul, he' j] at this
    field_simp
    rw [this]; ring
  · rw [← hc j₁]
    exact Ideal.mul_mem_mul hcP (Ideal.mem_span_singleton_self _)

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

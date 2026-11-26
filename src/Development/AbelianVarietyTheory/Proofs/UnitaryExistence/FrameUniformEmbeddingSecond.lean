module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkCoset

open scoped Matrix nonZeroDivisors

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latG_spec (D : D7) (V : HSp D) (g : GA D V) :
    (∀ v, v ∈ latG V g ↔ finVec V v ∈ latGHat V g) ∧
      ∀ z, z ∈ latGHat V g ↔ ∃ y ∈ latGHat V 1, (finHom V g).1 *ᵥ y = z := by
  let e : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map e
  have hfg : L.FG := V.standardTuple_isLattice.fg.map e
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E))) hspan
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : latHat V = AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold latHat AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, e x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hs := fun g : GA D V => AdLat.scale_latOf D.host.F D.host.E V.rank L (finHom V g) D.host.AA _
    hfg hsp (AA_ne_zero D) rfl
  set L' := Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ L, w = a • x} with hL'
  have h1 : (latG V g : Set (Fin V.rank → D.host.E)) = AdLat.latOf D.host.F (finHom V g).1 L' := by
    rw [← (hs g).1]
    unfold latG gLat
    rw [hhat]
    rfl
  have h2 : ∀ g : GA D V, (latGHat V g : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      (finHom V g).1.mulVec '' (AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E))) := by
    intro g
    rw [← (hs g).2.1]
    unfold latGHat gLat
    rw [hhat]
  have h3 : ∀ y, y ∈ latGHat V 1 ↔ y ∈ AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y
    rw [← SetLike.mem_coe, h2 1]
    simp only [map_one, Units.val_one, Set.mem_image, Matrix.one_mulVec, exists_eq_right, SetLike.mem_coe]
  refine ⟨fun v => ?_, fun z => ?_⟩
  · rw [← SetLike.mem_coe, h1, ← SetLike.mem_coe, h2 g]
    rfl
  · rw [← SetLike.mem_coe, h2 g]
    simp only [h3]
    rfl

theorem closure_congr {A : Type} [CommRing A] {n : ℕ} (k : Matrix (Fin n) (Fin n) A) (N : ℕ) (S : Set (Fin n → A))
    (h : ∀ z ∈ S, ∃ y ∈ AddSubgroup.closure S, k *ᵥ z = z + N • y) :
    ∀ z ∈ AddSubgroup.closure S, ∃ y ∈ AddSubgroup.closure S, k *ᵥ z = z + N • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw => exact h w hw
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [Matrix.mulVec_add, ex, ey, smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    exact ⟨-x', neg_mem hx', by rw [Matrix.mulVec_neg, ex, smul_neg]; abel⟩

theorem smul_congr {A : Type} [CommRing A] {n : ℕ} (k : Matrix (Fin n) (Fin n) A) (N : ℕ) (a : A) (z y : Fin n → A)
    (e : k *ᵥ z - z = N • y) : k *ᵥ (fun i => a * z i) = (fun i => a * z i) + N • fun i => a * y i := by
  change k *ᵥ (a • z) = a • z + N • (a • y)
  rw [Matrix.mulVec_smul, smul_comm N, ← smul_add, ← e, add_sub_cancel]

theorem level_latGHat {D : D7} (V : HSp D) (N : ℕ) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∀ z ∈ latGHat V 1, ∃ y ∈ latGHat V 1, (finHom V k).1 *ᵥ z = z + N • y := by
  have h1 : ∀ z, z ∈ gLat V 1 ↔ z ∈ latHat V := by
    intro z
    simp only [gLat, map_one, Units.val_one, Set.mem_image, Matrix.one_mulVec, exists_eq_right, SetLike.mem_coe]
  refine closure_congr _ N _ ?_
  rintro _ ⟨a, ha, z, hz, rfl⟩
  obtain ⟨y, hy, e⟩ := hk z ((h1 z).1 hz)
  exact ⟨_, AddSubgroup.subset_closure ⟨a, ha, y, (h1 y).2 hy, rfl⟩, smul_congr _ N _ z y e⟩

theorem rational_matrix {D : D7} (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) :
    ∃ δ₀ : GL (Fin V.rank) D.host.E,
      (∀ u v, herm (-V.gram.transpose) (δ₀.1 *ᵥ u) (δ₀.1 *ᵥ v) = herm (-V.gram.transpose) u v) ∧
      (∀ v, (finHom V δ).1 *ᵥ finVec V v = finVec V (δ₀.1 *ᵥ v)) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        archM V θ δ = δ₀.1.map τ := by
  obtain ⟨δ₀, hu, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  refine ⟨δ₀, fun u v => ?_, fun v => ?_, fun τ θ hθ => ?_⟩
  · have hu' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) δ₀.1 * V.gram * δ₀.1 = V.gram := hu
    have key : ∀ x y, herm (-V.gram.transpose) x y =
        -(((D.sp.cm.sig : D.host.E →+* D.host.E) ∘ y) ⬝ᵥ (V.gram *ᵥ x)) := by
      intro x y
      simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply,
        mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      change _ * _ * cc (y a) = cc (y a) * _
      ring
    have hm : (D.sp.cm.sig : D.host.E →+* D.host.E) ∘ (δ₀.1 *ᵥ v) =
        ((D.sp.cm.sig : D.host.E →+* D.host.E) ∘ v) ᵥ* Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) δ₀.1 := by
      rw [Formalism.UG.cT, Matrix.vecMul_transpose]
      funext i
      exact RingHom.map_mulVec _ _ _ i
    rw [key, key, hm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu']
  · funext i
    have hf : ∀ i j, (finHom V δ).1 i j = (1 : Af D.host.F) ⊗ₜ δ₀.1 i j := fun i j => by
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j) = _
      rw [he', Algebra.TensorProduct.map_tmul, map_one]
      rfl
    simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
      TensorProduct.tmul_sum]
  · ext i j
    change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    exact hθ.1 _

theorem nsmul_cancel (F : Type) [Field F] {A : Type} [AddCommGroup A] [Module F A] (N : ℕ) (hN : (N : F) ≠ 0)
    {x y : A} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

theorem finVec_div {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (x : Fin V.rank → D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (h : finVec V x = N • z) :
    ∃ w, finVec V w = z ∧ x = N • w := by
  have hE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : x = N • ((N : D.host.E)⁻¹ • x) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_inv_smul₀ hE]
  refine ⟨_, ?_, hx⟩
  have h2 : N • finVec V ((N : D.host.E)⁻¹ • x) = N • z := by
    rw [← h]
    conv_rhs => rw [hx]
    exact (AdLat.cap_fv_nsmul D.host.F N _).symm
  funext i
  exact nsmul_cancel D.host.F N hF (congrFun h2 i)

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : ∀ z ∈ Lh 1, ∃ y ∈ Lh 1, (f k).1 *ᵥ z = z + N • y)
    (hk' : ∀ z ∈ Lh 1, ∃ y ∈ Lh 1, (f k⁻¹).1 *ᵥ z = z + N • y) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a, a ∈ Lh 1 → (∃ w ∈ Lh u, x - (f u).1 *ᵥ a = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, e⟩ := hk' y hy
      refine ⟨(f k⁻¹).1 *ᵥ y, e ▸ add_mem hy (nsmul_mem hw N), ?_⟩
      rw [← hmul, ← hmul, mul_inv_cancel_right]
    · rintro ⟨y, hy, h⟩
      obtain ⟨w, hw, e⟩ := hk y hy
      refine ⟨(f k).1 *ᵥ y, e ▸ add_mem hy (nsmul_mem hw N), ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a ha ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  obtain ⟨y, hy, ey⟩ := hk a ha
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel


end GlobalTheory.MarkCoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem sab_extensions_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp K ⟶ Xo.X) (G G₂ : SAB H (Sp T)) (t t₂ : SAB H (Sp K)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T K))) (n₁ : SABMap t₂ Xo.univ.t x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T K))), ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  intro E _ _ _ H Dw l Xo T K _ _ _ _ _ _ x G G₂ t t₂ m₁ m₂ n₁ n₂
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m₁', hm₁⟩ := tr (Category.id_comp x).symm m₁
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ x (𝟙 _) n₁ m₁'
  obtain ⟨c, hc⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ (𝟙 _) n₂ k
  obtain ⟨c', hc'⟩ := tr (Category.id_comp _) c
  obtain ⟨ψ, hψ, hφ, hact⟩ := sab_group_iso_of_generic
    (existsUnique_hom_extension_semiAbelian_dvr (AbelianSubgroupFinite.finite_of_no_torsion abMulN_holds))
    E H T K G G₂ t m₂ c'
  obtain ⟨n, hn⟩ := Exist.CubicalExtension.sabMap_of_iso_of_extendGen
    (cubical_extends_and_extendGen forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
      GenExtend.existsUnique_gen_extend).2 E H T K G G₂ t m₂ c' ψ hψ hφ hact
  exact ⟨k, n, by rw [← hk, hm₁], by rw [hn, hφ, hc', hc]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatibleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_dvr_extensions_iso_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp K ⟶ Xo.X) (G G₂ : SAB H (Sp T)) (t t₂ : SAB H (Sp K)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T K))) (n₁ : SABMap t₂ Xo.univ.t x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T K))), ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.sab_extensions_iso | exact GlobalTheory.sab_extensions_iso | (intros; apply GlobalTheory.sab_extensions_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbelianNoTorsion

theorem finite_points_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro k _ _ A _ hA n hn hnk htor
  obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hpk : (p : k) ≠ 0 := fun h => hnk (by rw [Nat.cast_mul, h, zero_mul])
  have hfin : Finite (⊤ : Subgroup (𝟙_ (Over (Sp k)) ⟶ A)) :=
    GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.abMulN_holds k A p hA hp hpk ⊤ Set.univ
      isClosed_univ (fun x => ⟨fun _ => Set.subset_univ _, fun _ => Subgroup.mem_top x⟩)
      (fun x _ hx => htor x (by rw [pow_mul, hx, one_pow]))
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

end GlobalTheory.AbelianNoTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | exact GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion | (intros; apply GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevStab

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_isometry_of_hol {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (ha : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hhol : IsHolTo Set.univ (fun z => (e z).left)) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 ha hs hhol
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem map_mem_smul_top {R L L' : Type*} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (I : Ideal R) (f : L →ₗ[R] L') {x : L} (hx : x ∈ I • (⊤ : Submodule R L)) : f x ∈ I • (⊤ : Submodule R L') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_levAut (F : FamilyUnif Xo σ ty) {s : Sim D} {ρ : Xo.X ≅ Xo.X} (hρ : Xo.LevAut s ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ.hom = F.u j P') :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La, (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      ∀ a, gam (F.t i (s.f l.M a)) - F.t j a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
  obtain ⟨-, ν, hη, -⟩ := hρ
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ.hom ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  refine ⟨gam, hEF, fun a => ?_⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  have hxm : gam (F.t i (s.f l.M x)) - F.t j x ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) :=
    Submodule.sub_mem _ (map_mem_smul_top _ gam.toLinearMap (map_mem_smul_top _ _ (map_mem_smul_top _ _ hx₀)))
      (map_mem_smul_top _ _ hx₀)
  have hym : gam (F.t i (s.f l.M y)) - F.t j y ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
    obtain ⟨v, hv⟩ : ∃ v, gam (F.t i (s.f l.M y)) = F.t j y + l.M • v := by
      refine (div_eq_iff hP'.2.1 (F.ex_add j P' hP') (F.ex_ker j P' hP') hM0 _ _).1 ?_
      rw [hh, ← map_smul h, hx, ← F.ex_eta j P' hP' y hy, ← F.ex_eta i P hP _ (map_mem_smul_top _ _ hy)]
      apply Over.OverMorphism.ext
      rw [hβ]
      change (F.u i P ≫ (Xo.univ.eta (s.f l.M y)).left) ≫ ν.φ = F.u j P' ≫ (Xo.univ.eta y).left
      rw [Category.assoc, hη, ← Category.assoc, hu]
    rw [hv, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hM : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) hM
  have := Submodule.add_mem _ hxm hym
  rwa [sub_add_sub_comm, ← map_add, ← map_add, ← map_add, ← map_add] at this

end GlobalTheory.LevStab

end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
end

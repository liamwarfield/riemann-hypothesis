module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  first | exact @GlobalTheory.DegCnt.c_eq_quot_ideals | exact GlobalTheory.DegCnt.c_eq_quot_ideals | (intros; apply GlobalTheory.DegCnt.c_eq_quot_ideals <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotent
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.DatMove
open AdaptInv

theorem sup_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B A' B' : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ A' ↔ y ∈ B') (y : M) :
    t y ∈ A ⊔ A' ↔ y ∈ B ⊔ B' := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨t.symm a, (h _).1 (by simpa using ha), t.symm b, (h' _).1 (by simpa using hb), ?_⟩
    apply t.injective
    simp [hab]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨t a, (h _).2 ha, t b, (h' _).2 hb, by simp⟩

theorem sup_iff_of_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B C : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ C ↔ y ∈ C) {y : M}
    (hy : t y - y ∈ C) : y ∈ A ⊔ C ↔ y ∈ B ⊔ C := by
  rw [← sup_iff t h h' y]
  have h1 : t y - y ∈ A ⊔ C := Submodule.mem_sup_right hy
  rw [← Submodule.add_mem_iff_right _ h1]
  simp

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def push (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [hs]; exact F.iso a b
  zperp a := by rw [hs]; exact F.zperp a
  zz := by rw [hs]; exact F.zz
  hT := F.hT

variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)

theorem push_X (F : FlagD H r) : (push s hs F).X = F.X.map (s : V →ₗ[K] V) := by
  unfold FlagD.X FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem hermFrameMapIsometry_frameSpan (F G : FlagD H r) : V0 (push s hs F) (push s hs G) = (V0 F G).map (s : V →ₗ[K] V) := by
  unfold V0
  rw [push_X, push_X, Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Set.image_pair]
  rfl

theorem mem_map_iff (S : Submodule K V) (y : V) : s y ∈ S.map (s : V →ₗ[K] V) ↔ y ∈ S := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact s.injective h ▸ hx
  · exact fun h => ⟨y, h, rfl⟩

include hs in
theorem perp_map_iff (S : Submodule K V) (y : V) : s y ∈ perp H (S.map (s : V →ₗ[K] V)) ↔ y ∈ perp H S := by
  simp only [mem_perp_iff]
  constructor
  · intro h x hx
    rw [← hs]; exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact (hs _ _).trans (h x hx)

theorem push_X_iff (F : FlagD H r) (y : V) : s y ∈ (push s hs F).X ↔ y ∈ F.X := by
  rw [push_X, mem_map_iff]

variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

theorem hermIsometry_mem_flagPairDefinitePartLattice_iff (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (y : V) :
    s y ∈ flagPairDefinitePartLattice (push s hs F) (push s hs G) Λ' ↔ y ∈ flagPairDefinitePartLattice F G Λ := by
  have h1 := sup_iff s.toAddEquiv (A' := rs R (push s hs F).X) (B' := rs R F.X) h (push_X_iff s hs F) y
  simp only [flagPairDefinitePartLattice, latL, uPerp, wSp, Submodule.mem_inf, Submodule.restrictScalars_mem]
  rw [hermFrameMapIsometry_frameSpan, perp_map_iff s hs]
  refine and_congr (and_congr ?_ h1) Iff.rfl
  rw [push_X, push_X, ← Submodule.map_sup, perp_map_iff s hs]

theorem smulLat_iff {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V) :
    s y ∈ smulLat g Λ' ↔ y ∈ smulLat g Λ := by
  have hg : ∀ x, s (g • x) = g • s x := fun x => (s : V →ₗ[K] V).map_smul_of_tower g x
  constructor
  · rintro ⟨x, hx, h1⟩
    refine ⟨s.symm x, (h _).1 (by simpa using hx), s.injective ?_⟩
    rw [← h1]
    simpa using hg (s.symm x)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s x, (h _).2 hx, (hg x).symm⟩

theorem push_graph (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V × V) :
    (s.toAddEquiv.prodCongr s.toAddEquiv) y ∈ iotaGraph (push s hs F) (push s hs G) Λ' g ↔
      y ∈ iotaGraph F G Λ g := by
  simp only [iotaGraph, Submodule.mem_inf]
  refine and_congr (and_congr (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F h y.1) (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs F G h y.2)) ?_
  refine sup_iff _ (fun p => ?_) (fun p => and_congr (push_X_iff s hs G p.1) (push_X_iff s hs F p.2)) y
  refine and_congr (and_congr (h p.1) (h p.2)) ?_
  have := sup_iff s.toAddEquiv (A' := Λ' ⊓ rs R (push s hs F).X) (B' := Λ ⊓ rs R F.X) (smulLat_iff s h g)
    (fun y => and_congr (h y) (push_X_iff s hs F y)) (p.2 - p.1)
  rw [map_sub] at this
  exact this

theorem sameGr_push (F : FlagD H r) (hN : F.InN (s : V →ₗ[K] V)) : SameGr F (push s hN.1 F) := by
  intro a
  induction a using Fin.lastCases with
  | last => exact hN.2.2.2 _ F.zperp
  | cast a => exact hN.2.2.1 a

theorem flag_vector_mem_base_lattice (F G : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F G := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast a => exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_xa F a a.2))

theorem jointSpan_comm (F G : FlagD H r) : V0 F G = V0 G F := by
  unfold V0
  rw [sup_comm F.X, Set.pair_comm]

theorem herm_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem commonIsotropic_le_flagPairDefinitePartLattice {F G : FlagD H r} (hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0) (Λ : Submodule R V)
    {x : V} (hx : x ∈ II F G) : x ∈ flagPairDefinitePartLattice F G Λ := by
  refine ⟨⟨?_, Submodule.mem_sup_right hx.1⟩, ?_⟩
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w (Submodule.mem_sup_left hw))
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w hw)

end GlobalTheory.DegAsm.DatMove

namespace GlobalTheory.DegAsm
open AdaptInv DatMove

theorem datOf_move : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N g hE hA
  refine ⟨fun s Λ hN hG => ?_, ?_⟩
  · have hs : ∀ x y, H.B (s x) (s y) = H.B x y := hN.1
    have hF : SameGr F (push s hs F) := sameGr_push s F hN
    have hG' : SameGr G' (push s hs G) := hG
    have hΛ : ∀ y, s y ∈ s • Λ ↔ y ∈ Λ := fun y => by
      constructor
      · rintro ⟨x, hx, h⟩
        exact s.injective h ▸ hx
      · exact fun h => ⟨y, h, rfl⟩
    have hX : ∀ y, s y ∈ F.X ↔ y ∈ F.X := fun y => by
      have := push_X_iff s hs F y
      rwa [x_eq hF] at this
    have he : ∀ w, s (e w) - e w ∈ F.X := fun w =>
      hN.2.2.2 _ fun a => (hE.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) _
    refine ⟨Prod.ext ?_ ?_, ?_, ?_⟩
    · ext w
      refine sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) (fun y => ?_) hX (he w)
      rw [← flagFramesSameGraded_definitePartLattice_eq hG' hF]
      exact hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F hΛ y
    · ext w
      refine sup_iff_of_sub (s.toAddEquiv.prodCongr s.toAddEquiv)
        (C := (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)) (fun y => ?_)
        (fun p => and_congr (hX p.1) (hX p.2)) ⟨he w.1, he w.2⟩
      rw [← iotaGraph_eq hF hG']
      exact push_graph s hs F G hΛ _ y
    · ext w
      exact sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX (he w)
    · ext y
      refine and_congr_right fun hy => sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX ?_
      exact hN.2.2.2 y fun a => herm_zero
        ((mem_perp_iff _ _ _).1 hy _ (Submodule.mem_sup_left (e_mem_xa F a a.2)))
  · obtain ⟨-, h, h'⟩ := hA
    have h0 := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1.2.2.2.2.2.1
    have h1 : II N.F N.F' = II F G := by simp only [II, x_eq h, x_eq h']
    rw [h1, x_eq h, sitesCommonSpace_v0_eq_Vp h h'] at h0
    have hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0 := fun x hx => (h0 x hx.1).2 hx
    have hI' : ∀ x ∈ II G F, ∀ w ∈ V0 G F, H.B w x = 0 := fun x hx w hw =>
      hI x ⟨hx.2, hx.1⟩ w (jointSpan_comm G F ▸ hw)
    have hdec : ∀ y ∈ wSp F G, ∃ w, y - e w ∈ F.X := fun y hy => by
      have := (hE.2 y).1 fun a => herm_zero ((mem_perp_iff _ _ _).1 hy _ (flag_vector_mem_base_lattice F G a))
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨w, by simpa using hx⟩
    have hker : ∀ y ∈ wSp F G, ∀ y' ∈ wSp F G, y - y' ∈ F.X → y - y' ∈ II F G := fun y hy y' hy' hx =>
      (h0 _ hx).1 fun w hw => herm_zero ((mem_perp_iff _ _ _).1 (Submodule.sub_mem _ hy hy') w hw)
    have hw : wSp G F = wSp F G := by rw [wSp, jointSpan_comm]; rfl
    have hL : ∀ Λ : Submodule (𝓞 K) V, ∀ y ∈ flagPairDefinitePartLattice G F Λ, y ∈ wSp F G := fun Λ y hy => hw ▸ hy.2
    have key : ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' →
        flagPairDefinitePartLattice G F Λ ≤ flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) ≤ iotaGraph F G Λ' (g : 𝓞 K) := by
      intro Λ Λ' hd
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨w, hx⟩ := hdec y (hL _ y hy)
        have a1 : w ∈ (datOf F G e g Λ).1 := by
          have := Submodule.sub_mem (flagPairDefinitePartLattice G F Λ ⊔ rs (𝓞 K) F.X) (Submodule.mem_sup_left hy)
            (Submodule.mem_sup_right hx)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx', hmx⟩ := Submodule.mem_sup.1 a1
        have hmx : m + x = e w := hmx
        have a2 : y - m ∈ F.X := by
          have := F.X.add_mem hx hx'
          convert this using 1
          rw [← hmx]; abel
        have a3 := hker y (hL _ y hy) m (hL _ m hm) a2
        have := Submodule.add_mem _ (commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩) hm
        simpa using this
      · obtain ⟨w, hx⟩ := hdec y.1 (hL _ _ hy.1.1)
        obtain ⟨w', hx'⟩ := hdec y.2 hy.1.2.2
        have a1 : (w, w') ∈ (datOf F G e g Λ).2 := by
          have := Submodule.sub_mem (iotaGraph F G Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X))
            (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (x := y - (e w, e w')) ⟨hx, hx'⟩)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx2, hmx⟩ := Submodule.mem_sup.1 a1
        have hmx1 : m.1 + x.1 = e w := congrArg Prod.fst hmx
        have hmx2 : m.2 + x.2 = e w' := congrArg Prod.snd hmx
        have a2 : y.1 - m.1 ∈ F.X := by
          have := F.X.add_mem hx hx2.1
          convert this using 1
          rw [← hmx1]; abel
        have a2' : y.2 - m.2 ∈ F.X := by
          have := F.X.add_mem hx' hx2.2
          convert this using 1
          rw [← hmx2]; abel
        have a3 := hker _ (hL _ _ hy.1.1) _ (hL _ _ hm.1.1) a2
        have a3' := hker _ hy.1.2.2 _ hm.1.2.2 a2'
        have a4 : y - m ∈ iotaGraph F G Λ' (g : 𝓞 K) :=
          ⟨⟨commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩, commonIsotropic_le_flagPairDefinitePartLattice hI Λ' a3'⟩, Submodule.mem_sup_right ⟨a3.2, a3'.1⟩⟩
        have := Submodule.add_mem _ a4 hm
        simpa using this
    exact fun Λ Λ' hd => ⟨le_antisymm (key _ _ hd).1 (key _ _ hd.symm).1, le_antisymm (key _ _ hd).2 (key _ _ hd.symm).2⟩

end GlobalTheory.DegAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotentStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedDatum_invariant_under_unipotent : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  first | exact @GlobalTheory.DegAsm.datOf_move | exact GlobalTheory.DegAsm.datOf_move | (intros; apply GlobalTheory.DegAsm.datOf_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc

variable {K : Type} [Field K]

noncomputable def minor (bs : List (Kˣ × ℕ+)) (l : ℕ) : K :=
  (Matrix.of fun a b : Fin l => ptEntryL bs a b).det

theorem minor_zero (bs : List (Kˣ × ℕ+)) : minor bs 0 = 1 := by simp [minor]

theorem minor_lt (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) (h0 : 0 < l) (hl : l < s) :
    minor ((t, s) :: bs) l = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h0⟩ fun b => ?_
  have hb := b.2
  simp only [Matrix.of_apply, ptEntryL]
  split_ifs <;> first | rfl | omega

theorem minor_add (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (l : ℕ) :
    minor ((t, s) :: bs) (s + l) =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : K) ^ (s : ℕ)) * minor bs l := by
  have key : (Matrix.of fun a b : Fin (s + l) => ptEntryL ((t, s) :: bs) a b).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((Matrix.diagonal (fun _ : Fin s => (t : K))).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin s))) 0 0
        (Matrix.of fun a b : Fin l => ptEntryL bs a b) := by
    ext (a | a) (b | b)
    · have ha := a.2
      have hb := b.2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, ptEntryL, finSumFinEquiv_apply_left,
        Fin.val_castAdd, Matrix.fromBlocks_apply₁₁, id, Matrix.diagonal_apply, Fin.revPerm_apply,
        Fin.ext_iff, Fin.val_rev]
      split_ifs <;> first | rfl | omega
    · simp [ptEntryL]
    · simp [ptEntryL]
    · simp [ptEntryL]
  rw [minor, ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permute', Matrix.det_diagonal]
  simp [minor]

theorem sign_ne (u : ℤˣ) : ((u : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or u with e | e <;> simp [e]

theorem minor_self (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) :
    minor ((t, s) :: bs) s =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) * (t : K) ^ (s : ℕ) := by
  have := minor_add t s bs 0
  rwa [minor_zero, mul_one, Nat.add_zero] at this

theorem minor_self_ne (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) : minor ((t, s) :: bs) s ≠ 0 := by
  rw [minor_self]
  exact mul_ne_zero (sign_ne _) (pow_ne_zero _ t.ne_zero)

theorem count_lists (n : ℕ) : ∀ η : ℕ → K, ∃ T : Finset (List (Kˣ × ℕ+)), T.card ≤ 2 ^ n ∧
    ∀ bs : List (Kˣ × ℕ+), (bs.map (fun b => (b.2 : ℕ))).sum = n →
      (∀ l ≤ n, minor bs l = η l) → bs ∈ T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro η
  by_cases hex : ∃ (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)),
      (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum = n ∧ ∀ l ≤ n, minor ((t, s) :: bs) l = η l
  · obtain ⟨t₀, s, bs₀, hs, h₀⟩ := hex
    have hsp := s.pos
    obtain ⟨T, hT, hT'⟩ := ih (n - s) (by omega) (fun l => η (s + l) / η s)
    let c : K := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ)
    have hc : c ≠ 0 := sign_ne _
    let R := (Polynomial.nthRoots s (η s / c)).toFinset
    have hR : R.card ≤ s := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    refine ⟨Finset.image₂ (fun x bs => ((if h : x = 0 then 1 else Units.mk0 x h), s) :: bs) R T,
      ?_, ?_⟩
    · refine (Finset.card_image₂_le _ _ _).trans ?_
      calc R.card * T.card ≤ 2 ^ (s : ℕ) * 2 ^ (n - s) :=
            Nat.mul_le_mul (hR.trans (Nat.lt_two_pow_self).le) hT
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    · rintro (_ | ⟨⟨t, s'⟩, bs⟩) hsum h
      · simp only [List.map_nil, List.sum_nil] at hsum
        omega
      simp only [List.map_cons, List.sum_cons] at hsum
      have hsp' := s'.pos
      have e : s' = s := by
        apply PNat.eq
        rcases lt_trichotomy (s' : ℕ) s with h1 | h1 | h1
        · exact absurd ((h s' (by omega)).trans ((h₀ s' (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp' h1))) (minor_self_ne _ _ _)
        · exact h1
        · exact absurd ((h₀ s (by omega)).trans ((h s (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp h1))) (minor_self_ne _ _ _)
      subst e
      have h1 := h s' (by omega)
      refine Finset.mem_image₂.2 ⟨t, ?_, bs, hT' bs (by omega) fun l hl => ?_, ?_⟩
      · simp only [R, Multiset.mem_toFinset, Polynomial.mem_nthRoots hsp]
        rw [← h1, minor_self, eq_div_iff hc, mul_comm]
      · rw [← h _ (by omega), ← h1, minor_add, ← minor_self t s' bs,
          mul_div_cancel_left₀ _ (minor_self_ne _ _ _)]
      · simp [t.ne_zero]
  · refine ⟨{[]}, by simpa using Nat.one_le_two_pow, ?_⟩
    rintro (_ | ⟨⟨t, s⟩, bs⟩) hsum h
    · simp
    · exact absurd ⟨t, s, bs, by simpa using hsum, h⟩ hex

end GlobalTheory.SignedBlockCount

namespace GlobalTheory


open Formalism.MainNotions.S.Loc SignedBlockCount in
theorem signed_block_count : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  intro K _ j δ
  choose T hT hT' using count_lists (K := K) j
  let η : (Fin j → ℤˣ) → ℕ → K := fun sgn l =>
    if hl : l ≤ j then δ l / ∏ b : Fin l, ((sgn (Fin.castLE hl b) : ℤ) : K) else 0
  let U : Finset (Matrix (Fin j) (Fin j) K) := Finset.univ.biUnion fun sgn : Fin j → ℤˣ =>
    (T (η sgn)).image fun bs => Matrix.of fun a b => ptEntryL bs a b * ((sgn b : ℤ) : K)
  have hU : U.card ≤ 8 ^ j := by
    refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ j)
      fun sgn _ => Finset.card_image_le.trans (hT _)).trans ?_
    simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_units_int, Finset.prod_const,
      Fintype.card_fin]
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine (Set.encard_le_encard (t := (U : Set _)) ?_).trans ?_
  · rintro P ⟨⟨w, sgn, hP⟩, hδ⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨sgn, Finset.mem_univ _,
      Finset.mem_image.2 ⟨w.blocks, hT' _ _ w.size fun l hl => ?_, ?_⟩⟩)
    · simp only [η, dif_pos hl]
      rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun b _ => sign_ne _), ← hδ l hl, mul_comm, minor,
        ← Matrix.det_mul_row]
      congr 1
      ext a b
      simp [hP, Pt.mat, mul_comm]
    · ext a b
      simp [hP, Pt.mat]
  · rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hU

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedBlockAntidiagWithLeadingMinorsEncardLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  first | exact @GlobalTheory.signed_block_count | exact GlobalTheory.signed_block_count | (intros; apply GlobalTheory.signed_block_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfMulMem
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.NormOneCount

theorem le_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 := hp.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hP : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, Nat.add_sub_cancel]
    generalize (q + 1) ^ k = P at hP ⊢
    have hPP : P ≤ P ^ 2 := by nlinarith
    refine ⟨?_, fun ho => ?_⟩
    · have h1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * (2 * q ^ 2) := Nat.mul_le_mul hPP h1
        _ = _ := by ring
    · have ho' : Odd (q + 1) := (Nat.odd_mul.1 ho).2
      have hq2 : 2 ≤ q := by
        obtain ⟨m, hm⟩ := ho'
        omega
      have h1 : q + 1 ≤ q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * q ^ 2 := Nat.mul_le_mul hPP h1
        _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    refine ⟨?_, fun ho => ?_⟩
    · rcases Nat.even_or_odd a with hea | hoa
      · have hob : Odd b := by
          rcases Nat.even_or_odd b with heb | hob
          · have := Nat.dvd_gcd hea.two_dvd heb.two_dvd
            rw [hab.gcd_eq_one] at this
            omega
          · exact hob
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hob)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hoa) ihb.1
          _ = _ := by ring
    · obtain ⟨h1, h2⟩ := Nat.odd_mul.1 ho
      calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)
        _ = _ := by ring

theorem card_torsion_le (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K)) := hg ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K)) :=
    h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective
  have h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K)) :=
    IsPrimitiveRoot.coe_units_iff.2 h2
  have h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K)) :=
    h3.map_of_injective (RingOfIntegers.coe_injective)
  have hpos : 0 < Nat.card (Units.torsion K) := Nat.card_pos
  have h5 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4
    (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self] at h5
  exact (le_totient_sq _).1.trans (by gcongr)

variable {K : Type} [Field K] [NumberField K]

theorem isIntegral_of_mul_mem {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by
  have hne : ipow 𝔞 1 ≠ ⊥ := by
    unfold ipow
    rw [zpow_one]
    intro h0
    exact (FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  have hfg : (ipow 𝔞 1).FG := by
    unfold ipow
    exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : IsIntegral (𝓞 K) u :=
    isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)
  exact isIntegral_trans u h1

theorem exists_torsion [StarRing K] (hK : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    {𝔞 𝔞' : Ideal (𝓞 K)} (h : 𝔞' ≠ ⊥) {c d : K} (hc : c * star c = 1) (hd : d * star d = 1)
    (h1 : ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) (h2 : ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) :
    ∃ ζ : Units.torsion K, c = algebraMap (𝓞 K) K ((ζ : (𝓞 K)ˣ) : 𝓞 K) * d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have i1 : IsIntegral ℤ (c / d) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht
  have i2 : IsIntegral ℤ (d / c) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d := ⟨⟨c / d, i1⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c := ⟨⟨d / c, i2⟩, rfl⟩
  have hm : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, ha, hb]
    field_simp
  have hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1 := fun φ e he => by
    have h3 := congrArg (fun z => ‖φ z‖) he
    simp only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3
    nlinarith [norm_nonneg (φ e)]
  refine ⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩
  · show w (algebraMap (𝓞 K) K a) = 1
    rw [ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]
  · show c = algebraMap (𝓞 K) K a * d
    rw [ha]
    field_simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ x : ℝ, 1 ≤ x → ((({c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * x ^ (2 * (2 + cf K))) := by
  intro K _ _ _ hK x hx
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K x hx
  set A := {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} with hA
  let c0 : Ideal (𝓞 K) × Ideal (𝓞 K) → K := fun p =>
    if h : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow p.1 1 ↔ t ∈ ipow p.2 1 then h.choose else 0
  let g : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Units.torsion K → K := fun q =>
    algebraMap (𝓞 K) K ((q.2 : (𝓞 K)ˣ) : 𝓞 K) * c0 q.1
  have hB : ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))).Finite :=
    (hfin.prod hfin).prod Set.finite_univ
  have hsub : {c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧
      (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1} ⊆
      g '' ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))) := by
    rintro c ⟨hc, 𝔞, 𝔞', h1, h2, h3, h4, h5⟩
    have hex : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := ⟨c, hc, h5⟩
    obtain ⟨ζ, hζ⟩ := exists_torsion hK.2.1 h2 hc hex.choose_spec.1 h5 hex.choose_spec.2
    refine ⟨((𝔞, 𝔞'), ζ), ⟨⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, trivial⟩, ?_⟩
    simp only [g, c0, dif_pos hex]
    exact hζ.symm
  have henc := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  rw [← hB.cast_ncard_eq, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ] at henc
  refine (ENat.toENNReal_le.2 henc).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hw : (Nat.card (Units.torsion K) : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 := by
    have h1 := card_torsion_le K
    rw [hd] at h1
    have h2 : (Nat.card (Units.torsion K) : ℝ) ≤ 2 * (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) ^ 2 := by
      exact_mod_cast h1
    linarith
  have hA' : (A.ncard : ℝ) ≤ x ^ (2 + cf K) :=
    hle.trans (Real.rpow_le_rpow_of_exponent_le hx (by unfold cf; linarith))
  have hx0 : 0 < x := by linarith
  push_cast
  calc (A.ncard : ℝ) * A.ncard * Nat.card (Units.torsion K)
      ≤ x ^ (2 + cf K) * x ^ (2 + cf K) * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hx0, two_mul (2 + cf K)]; ring

end GlobalTheory.DegCnt.NormOneCount
end
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.PerDat

theorem sum_le_of_fibres {ι α : Type} [DecidableEq α] (s : Finset ι) (k : ι → α) (f : ι → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hM : ((s.image k).card : ℝ) ≤ M) (h : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => k i = k i₀), f i ≤ B) :
    ∑ i ∈ s, f i ≤ M * B := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := s.image k) (fun i hi => Finset.mem_image_of_mem k hi)]
  refine (Finset.sum_le_card_nsmul _ _ B fun y hy => ?_).trans ?_
  · obtain ⟨i₀, hi, rfl⟩ := Finset.mem_image.1 hy
    exact h i₀ hi
  · rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hM hB

section Carry
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Carr (s : V ≃ₗ[K] V) (A B : FlagD H r) : Prop := ∀ a : Fin (r + 1), s (A.e a) - B.e a ∈ B.Xa a.val

theorem Carr.map_xa {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : Carr s A B) (n : ℕ) {x : V} (hx : x ∈ A.Xa n) :
    s x ∈ B.Xa n := by
  have : A.Xa n ≤ (B.Xa n).comap (s : V →ₗ[K] V) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have := Submodule.add_mem _ (AdaptInv.xa_mono B (le_of_lt hb) (h b.castSucc)) (AdaptInv.e_mem_xa B b hb)
    simpa using this
  exact this hx

theorem Carr.trans {s t : V ≃ₗ[K] V} {A B C : FlagD H r} (h : Carr s A B) (h' : Carr t B C) :
    Carr (t * s) A C := fun a => by
  have := Submodule.add_mem _ (h'.map_xa _ (h a)) (h' a)
  simpa using this

theorem carr_of_sameGr {A B : FlagD H r} (h : SameGr B A) : Carr 1 A B := fun a => h a

theorem carr_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s A B := fun a => by
  rw [h a, sub_self]; exact zero_mem _

theorem carr_inv_of_eq {s : V ≃ₗ[K] V} {A B : FlagD H r} (h : ∀ a, s (A.e a) = B.e a) : Carr s⁻¹ B A :=
  carr_of_eq fun a => by rw [← h a]; exact s.symm_apply_apply _

theorem carr_of_inN {s : V ≃ₗ[K] V} {A : FlagD H r} (h : A.InN (s : V →ₗ[K] V)) : Carr s A A := fun a => by
  induction a using Fin.lastCases with
  | last => exact GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem h
  | cast b => exact h.2.2.1 b

theorem flagFrameVector_mem_commonSubspace (A B : FlagD H r) (a : Fin (r + 1)) : A.e a ∈ V0 A B := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b => exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X A b))

end Carry

section Main
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] {H : HermSpace K V} {HW : HermSpace K W} {e : W →ₗ[K] V} {r : ℕ}

omit [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
theorem finrank_wt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (he : IsEmb F HW e) (hN : Adapt F G 𝔡 N) : Module.finrank K N.Wt = Module.finrank K W := by
  obtain ⟨hfull, hlift, -⟩ := GlobalTheory.DegCnt.NF.geometry K V H hK r N
  have hX : N.F.X = F.X := AdaptInv.x_eq hN.2.1
  have hV : V0 N.F N.F' = V0 F G := AdaptInv.sitesCommonSpace_v0_eq_Vp hN.2.1 hN.2.2
  have hperp : ∀ (w : W) (a : Fin (r + 1)), H.B (F.e a) (e w) = 0 :=
    fun w => (he.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
  have hinj : Function.Injective e := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    refine HW.nondeg w fun y => ?_
    rw [← he.1, hw]; simp
  have h1 : LinearMap.range e ⊓ F.X = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    have : w = 0 := HW.nondeg w fun y => by
      rw [← he.1]
      exact GlobalTheory.UnipStab.orth_X F (fun a => hperp y _) hw
    simp [this]
  have h2 : N.Wt ⊓ F.X = ⊥ := by
    rw [eq_bot_iff, ← hlift.2.1, ← hX]
    rintro x ⟨hx, hx'⟩
    exact ⟨hx, (hfull.2.2.2.2.2.1 x hx').1 (hlift.1 x hx)⟩
  have h3 : N.Wt ⊔ F.X = LinearMap.range e ⊔ F.X := by
    apply le_antisymm
    · refine sup_le (fun x hx => (he.2 x).1 fun a => hlift.1 x hx _ ?_) le_sup_right
      rw [hV]; exact flagFrameVector_mem_commonSubspace F G a
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, hx, hx'⟩ := hfull.2.2.2.2.2.2.2.1 (e w) fun a => by
        have a1 : N.F.e a - F.e a ∈ F.X := AdaptInv.xa_mono F (Nat.lt_succ_iff.1 a.2) (hN.2.1 a)
        have a2 := GlobalTheory.UnipStab.orth_X F (fun a => hperp w _) a1
        simpa [hperp w a] using a2
      have a3 : e w - x ∈ N.Wt ⊔ F.X := by
        refine (sup_le_sup_left (show II N.F N.F' ≤ F.X from hX ▸ inf_le_left) _) (hlift.2.2 _ hx')
      have := Submodule.add_mem _ a3 (Submodule.mem_sup_right (hX ▸ hx))
      simpa using this
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt F.X
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) F.X
  rw [h2, h3] at d1
  rw [h1, LinearMap.finrank_range_of_inj hinj] at d2
  omega

theorem one_class (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F : FlagD H r} {𝔡 : Ideal (𝓞 K)} {g : ℕ} {Λ : Submodule (𝓞 K) V}
    {ι : Type} (s : Finset ι) (G : ι → FlagD H r) (N : ι → NF H r) (G₀ : FlagD H r) (N₀ : NF H r) (hg : 1 ≤ g)
    (he : IsEmb F HW e) (h₀ : Adapt F G₀ 𝔡 N₀) (ht₀ : N₀.IsTerm g Λ)
    (hN : ∀ i ∈ s, Adapt F (G i) 𝔡 (N i) ∧ (N i).IsTerm g Λ ∧ N₀.j = (N i).j ∧ N₀.c = (N i).c ∧ N₀.T = (N i).T ∧
      pairM N₀.F N₀.F' N₀.j = pairM (N i).F (N i).F' (N i).j ∧ datOf F (G i) e g Λ = datOf F G₀ e g Λ)
    (hinj : ∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') :
    ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.NT ^ 2 * ((N₀.Del / N₀.gI g Λ) ^ ((Module.finrank K W : ℝ) / 2) *
      N₀.Del ^ (cf K + 2) * (N₀.Db * N₀.Del * N₀.NT) ^ (10000 * (r + 1) ^ 3)) := by
  have hex : ∀ i ∈ s, ∃ σ : V ≃ₗ[K] V, F.InN (σ : V →ₗ[K] V) ∧
      ∀ a, σ (N₀.F.e a) = (N i).F.e a ∧ σ (N₀.F'.e a) = (N i).F'.e a := fun i hi => by
    obtain ⟨a1, -, a2, a3, a4, a5, -⟩ := hN i hi
    exact GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent K V H hK r F N₀ (N i) h₀.2.1 a1.2.1 a2 a3 a4 a5
  choose! σ hσ hσe using hex
  have hcan : ∀ i, σ i • ((σ i)⁻¹ • Λ) = Λ := fun i => smul_inv_smul _ _
  have hmove : ∀ i ∈ s, omI F (G i) 𝔡 Λ ≤ N₀.om ((σ i)⁻¹ • Λ) ∧ N₀.IsTerm g ((σ i)⁻¹ • Λ) := fun i hi => by
    obtain ⟨a1, a2, -⟩ := hN i hi
    obtain ⟨N', b1, -, -, -, b2, -, b3⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N₀ (σ i) ((mem_isomGrp H _).2 (hσ i hi).1)
    obtain ⟨c1, c2, -⟩ := b3 g ((σ i)⁻¹ • Λ)
    rw [hcan] at c1 c2
    have hA : Adapt F (G i) 𝔡 N' := by
      refine ⟨b2.trans h₀.1, fun a => ?_, fun a => ?_⟩
      · rw [(b1 a).1, (hσe i hi a).1]; exact a1.2.1 a
      · rw [(b1 a).2, (hσe i hi a).2]; exact a1.2.2 a
    refine ⟨c1 ▸ ((WeightInf.main K V H hK r).2 F (G i) 𝔡 Λ).2.1 N' hA, c2.1 ?_⟩
    have haa : N'.aa = (N i).aa := by
      funext a; simp only [NF.aa, hA.1, a1.1]
    rw [((adapt_invariants K V H hK r F (G i) 𝔡 N' hA).2.2.2.2.2.2.2.2 g Λ).1, haa]
    exact ((adapt_invariants K V H hK r F (G i) 𝔡 (N i) a1).2.2.2.2.2.2.2.2 g Λ).1.1 a2
  refine (Finset.sum_le_sum fun i hi => (hmove i hi).1).trans ?_
  rw [← finrank_wt hK he h₀]
  refine GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le K V H hK r N₀ g Λ ι s (fun i => (σ i)⁻¹ • Λ) hg ht₀ (fun i hi => ?_) ?_
  · obtain ⟨a1, -, -, -, -, -, a2⟩ := hN i hi
    have hc : Carr (1 * (σ i * 1)) G₀ (G i) :=
      ((carr_of_sameGr (AdaptInv.sameGr_symm h₀.2.2)).trans (carr_of_eq fun a => (hσe i hi a).2)).trans
        (carr_of_sameGr a1.2.2)
    rw [one_mul, mul_one] at hc
    obtain ⟨d1, d2⟩ := GlobalTheory.T.embeddedDatum_invariant_under_unipotent K V W H HW e hK r F G₀ (G i) 𝔡 N₀ g he h₀
    obtain ⟨e1, -, e2⟩ := d1 (σ i) ((σ i)⁻¹ • Λ) (hσ i hi) hc
    rw [hcan] at e1 e2
    obtain ⟨f1, f2⟩ := d2 ((σ i)⁻¹ • Λ) Λ (e1.symm.trans a2)
    refine ⟨(hmove i hi).2, ?_, ?_, ?_⟩
    · rw [AdaptInv.latL_eq h₀.2.1 h₀.2.2, AdaptInv.latL_eq h₀.2.1 h₀.2.2, e2]
    · rw [AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, AdaptInv.flagFramesSameGraded_definitePartLattice_eq h₀.2.2 h₀.2.1, f1]
    · rw [AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, AdaptInv.iotaGraph_eq h₀.2.1 h₀.2.2, f2]
  · rintro i hi i' hi' ⟨ρ, hρ, hρe⟩
    obtain ⟨r1, r2⟩ := (GlobalTheory.UnipStab.mem_R N₀ ρ).1 hρ
    refine hinj i hi i' hi' ⟨σ i' * (ρ * (σ i)⁻¹), GlobalTheory.UnipStab.inN_mul (hσ i' hi') (GlobalTheory.UnipStab.inN_mul
      (AdaptInv.inN_of (AdaptInv.sameGr_symm h₀.2.1) _ r1) (GlobalTheory.UnipStab.inN_inv (hσ i hi))), ?_, ?_⟩
    · rw [mul_smul, mul_smul]
      exact (congrArg (fun L => σ i' • L) hρe).trans (hcan i')
    · have hc : Carr (1 * (σ i' * (ρ * ((σ i)⁻¹ * 1)))) (G i) (G i') :=
        ((((carr_of_sameGr (AdaptInv.sameGr_symm (hN i hi).1.2.2)).trans
          (carr_inv_of_eq fun a => (hσe i hi a).2)).trans (carr_of_inN r2)).trans
          (carr_of_eq fun a => (hσe i' hi' a).2)).trans (carr_of_sameGr (hN i' hi').1.2.2)
      rw [one_mul, mul_one] at hc
      exact hc
end Main

section Count
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def sqM (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) : Matrix (Fin j) (Fin j) K :=
  fun a b => H.B (N.F.e (Fin.castLE hj a)) (N.F'.e (Fin.castLE hj b))

theorem sqM_shape (N : NF H r) (j : ℕ) (hj : j ≤ r + 1) (h : N.j = j) :
    ∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, sqM N j hj a b = w.mat a b * ((sgn b : ℤ) : K) := by
  subst h
  exact ⟨N.w, N.sgn, N.pair⟩

theorem pairM_eq {N N' : NF H r} {j : ℕ} {hj : j ≤ r + 1} (h : sqM N j hj = sqM N' j hj) :
    pairM N.F N.F' j = pairM N'.F N'.F' j := by
  funext a b
  unfold pairM
  split_ifs with hab
  · exact congrFun (congrFun h ⟨a.val, hab.1⟩) ⟨b.val, hab.2⟩
  · rfl

end Count

end GlobalTheory.DegAsm.PerDat

namespace GlobalTheory.DegAsm
open PerDat

theorem sum_weights_per_datum : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (g j T x : ℕ) (δ : ℕ → K) (Λ : Submodule (𝓞 K) V) (d : Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W)) (Del Db : ℝ) (ι : Type) (s : Finset ι) (G : ι → FlagD H r), 1 ≤ g → 1 ≤ x → 1 ≤ Del → 1 ≤ Db → IsEmb F HW e → (∀ i ∈ s, ∃ N : NF H r, Adapt F (G i) 𝔡 N ∧ N.IsTerm g Λ ∧ N.j = j ∧ N.T = T ∧ N.Del = Del ∧ N.Db = Db ∧ N.gI g Λ = x) → (∀ i ∈ s, lab F (G i) j = δ ∧ datOf F (G i) e g Λ = d) → (∀ i ∈ s, ∀ i' ∈ s, FrEqv F Λ (G i) (G i') → i = i') → ∑ i ∈ s, omI F (G i) 𝔡 Λ ≤ datBd K (Module.finrank K W) r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F 𝔡 g j T x δ Λ d Del Db ι s G hg hx hDel hDb he hN hd hinj
  have hDel0 : 0 < Del := by linarith
  have hDb0 : 0 < Db := by linarith
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₁, hi₁⟩
  · rw [Finset.sum_empty]; unfold datBd; positivity
  haveI : Nonempty (NF H r) := ⟨(hN i₁ hi₁).choose⟩
  choose! N hA ht hj hT hD hB hI using hN
  have hjr : j ≤ r := hj i₁ hi₁ ▸ (N i₁).j_le
  have hjr' : j ≤ r + 1 := by omega
  have c1 : ((s.image fun i => sqM (N i) j hjr').card : ℝ) ≤ 8 ^ r := by
    have h1 := GlobalTheory.T.signedBlockAntidiag_with_leadingMinors_encard_le K j δ
    have h2 := (Set.encard_le_encard (s := ((s.image fun i => sqM (N i) j hjr' : Finset _) : Set _)) ?_).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard] at h2
      have h3 : (s.image fun i => sqM (N i) j hjr').card ≤ 8 ^ j := by exact_mod_cast h2
      have h4 : 8 ^ j ≤ 8 ^ r := Nat.pow_le_pow_right (by norm_num) hjr
      exact_mod_cast h3.trans h4
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hP)
      refine ⟨sqM_shape _ _ _ (hj i hi), fun l hl => ?_⟩
      have hl' : l ≤ r + 1 := by omega
      rw [← (hd i hi).1, lab, dite_eq_left ⟨hl, hl'⟩, ← AdaptInv.dl_eq (hA i hi).2.1 (hA i hi).2.2]
      rfl
  have c2 : ((s.image fun i => (N i).c).card : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K)) := by
    have h1 := GlobalTheory.DegCnt.NormOneCount.main K hK Del hDel
    have h2 := (ENat.toENNReal_le.2
      (Set.encard_le_encard (s := ((s.image fun i => (N i).c : Finset _) : Set _)) ?_)).trans h1
    · rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
      exact h2
    · intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
      refine ⟨(N i).c_norm, ?_⟩
      rw [← hD i hi]
      exact GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le K V H hK r (N i) g Λ hg (ht i hi)
  have c3 : ((s.image fun i => (sqM (N i) j hjr', (N i).c)).card : ℝ) ≤
      8 ^ r * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * Del ^ (2 * (2 + cf K))) := by
    have h1 : (s.image fun i => (sqM (N i) j hjr', (N i).c)).card ≤
        (s.image fun i => sqM (N i) j hjr').card * (s.image fun i => (N i).c).card := by
      rw [← Finset.card_product]
      refine Finset.card_le_card fun p hp => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩
    refine le_trans ?_ (mul_le_mul c1 c2 (by positivity) (by positivity))
    exact_mod_cast h1
  refine (sum_le_of_fibres s _ _ (((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ 2 * ((Del / x) ^ ((Module.finrank K W : ℝ) / 2) *
      Del ^ (cf K + 2) * (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3))) _ (by positivity) c3
      fun i₀ hi₀ => ?_).trans (le_of_eq ?_)
  · have := one_class (HW := HW) (e := e) hK
      (s.filter fun i => (sqM (N i) j hjr', (N i).c) = (sqM (N i₀) j hjr', (N i₀).c)) G N (G i₀) (N i₀) hg he
      (hA i₀ hi₀) (ht i₀ hi₀) (fun i hi => ?_)
      fun i hi i' hi' => hinj i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1
    · rw [NF.NT, hT i₀ hi₀, hD i₀ hi₀, hB i₀ hi₀, hI i₀ hi₀] at this
      exact this
    · obtain ⟨hi, hk⟩ := Finset.mem_filter.1 hi
      obtain ⟨k1, k2⟩ := Prod.mk.inj hk
      refine ⟨hA i hi, ht i hi, (hj i₀ hi₀).trans (hj i hi).symm, k2.symm, (hT i₀ hi₀).trans (hT i hi).symm, ?_,
        (hd i hi).2.trans (hd i₀ hi₀).2.symm⟩
      rw [hj i₀ hi₀, hj i hi]
      exact pairM_eq k1.symm
  · unfold datBd
    rw [show 3 * cf K + 6 = 2 * (2 + cf K) + (cf K + 2) by ring, Real.rpow_add hDel0 (2 * (2 + cf K))]
    generalize (Db * Del * (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (10000 * (r + 1) ^ 3) = y
    generalize Del ^ (2 * (2 + cf K)) = y₁
    generalize Del ^ (cf K + 2) = y₂
    generalize (Del / x) ^ ((Module.finrank K W : ℝ) / 2) = y₃
    ring

end GlobalTheory.DegAsm

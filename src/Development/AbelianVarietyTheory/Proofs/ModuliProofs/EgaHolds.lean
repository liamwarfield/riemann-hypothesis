module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.ega_holds : GlobalTheory.LN.Ega :=
  GlobalTheory.T.extension_of_abelian_schemes GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModels
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GlobalModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isLocalization_away {S A : ℕ} (hS : 0 < S) (b : RZ H 1 A →+* RZ H S A)
    (hb : IsInc (RZ H 1 A).subtype (RZ H S A).subtype b) :
    @IsLocalization.Away (RZ H 1 A) _ (S : RZ H 1 A) (RZ H S A) _ b.toAlgebra := by
  letI := b.toAlgebra
  have hS' : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hb' : ∀ x, ((b x : RZ H S A) : ℂ) = x := hb
  have key : ∀ z ∈ RZ H S A, ∃ (n : ℕ) (a : RZ H 1 A), z * (S : ℂ) ^ n = a := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inl rfl)⟩, by simp⟩
      · exact ⟨1, 1, by simp [hS']⟩
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inr (Or.inr rfl))⟩, by simp⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      refine ⟨n + m, a * (S : RZ H 1 A) ^ m + c * (S : RZ H 1 A) ^ n, ?_⟩
      push_cast
      rw [← ha, ← hc]; ring
    | neg x _ hx =>
      obtain ⟨n, a, ha⟩ := hx
      exact ⟨n, -a, by push_cast; rw [← ha]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      exact ⟨n + m, a * c, by push_cast; rw [← ha, ← hc]; ring⟩
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun x y h => ⟨0, ?_⟩)
  · refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext ?_)
    simp [hS']
  · obtain ⟨n, a, ha⟩ := key z.1 z.2
    refine ⟨n, a, Subtype.ext ?_⟩
    rw [map_natCast]
    refine Eq.trans ?_ (ha.trans (hb' a).symm)
    push_cast
    rfl
  · have : x = y := Subtype.ext ((hb' x).symm.trans ((congrArg Subtype.val h).trans (hb' y)))
    rw [this]

theorem span_natCast_eq_top {R I : Type} [CommRing R] (a : I → ℕ) (h : ∀ p : ℕ, p.Prime → ∃ i, ¬ p ∣ a i) :
    Ideal.span (Set.range fun i => (a i : R)) = ⊤ := by
  set J := Ideal.span (Set.range fun i => (a i : R))
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (J.comap (Int.castRingHom R))).principal
  have hd : ∀ i, g ∣ (a i : ℤ) := fun i => by
    rw [← Ideal.mem_span_singleton]
    change _ ∈ Submodule.span ℤ {g}
    rw [← hg, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h1 : g.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨i, hi⟩ := h p hp
    exact hi (hpg.trans (Int.natAbs_dvd_natAbs.mpr (hd i)))
  have hu : IsUnit g := Int.isUnit_iff_natAbs_eq.mpr h1
  have hm : g ∈ J.comap (Int.castRingHom R) := hg ▸ Submodule.mem_span_singleton_self g
  exact Ideal.eq_top_of_isUnit_mem _ hm (hu.map _)

theorem finite_parts (l : Level H) : Finite {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p} := by
  refine Finite.of_injective (fun x => (⟨x.1.M, ?_⟩ : Set.Iic l.M)) ?_
  · obtain ⟨p, -, -, h, -⟩ := x.2
    exact h ▸ Nat.div_le_self _ _
  · rintro ⟨⟨M, _, _, Mb, _, _, _, A, _⟩, p, _, h₁, _, h₃⟩ ⟨⟨M', _, _, Mb', _, _, _, A', _⟩, p', _, h₁', _, h₃'⟩ h
    obtain rfl : M = M' := congrArg Subtype.val h
    obtain rfl : A = A' := h₁.trans h₁'.symm
    obtain rfl : Mb = Mb' := h₃.trans h₃'.symm
    rfl

theorem exists_map_to_base {U U'' U₀ : Scheme.{0}} {F F'' F₀ O O'' O₀ R V : Type} [Field F] [Field F''] [Field F₀]
    [CommRing O] [CommRing O''] [CommRing O₀] [CommRing R] [CommRing V]
    {c : U ⟶ Sp F} {c'' : U'' ⟶ Sp F''} {c₀ : U₀ ⟶ Sp F₀} {t : SAB H U} {t'' : SAB H U''} {t₀ : SAB H U₀}
    {β : O →+* F} {β'' : O'' →+* F''} {β₀ : O₀ →+* F₀} {ω : R →+* F}
    {C' : Cpt c t β} {C'' : Cpt c'' t'' β''} {C₀ : Cpt c₀ t₀ β₀} {C₁ : Cpt c t ω}
    {b'' : O →+* O''} {r'' : U'' ⟶ U} {ν'' : SABMap t'' t r''} (A'' : C''.Above C' b'' r'' ν'')
    {b₀ : O₀ →+* R} {r : U ⟶ U₀} {ν : SABMap t t₀ r} (A₁ : C₁.Above C₀ b₀ r ν)
    (b₁ : O →+* R) [Mono (spMap b₁)] (hω : ω.comp b₁ = β)
    (f : pullback C'.s (spMap b₁) ⟶ C₁.X) (t₁ : SAB H (pullback C'.s (spMap b₁)))
    (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ C₁.t f)
    (h₁ : ∀ g : U ⟶ pullback C'.s (spMap b₁), g ≫ pullback.fst _ _ = C'.j → g ≫ f = C₁.j)
    (h₂ : ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = C₁.m.φ)
    (b : O'' →+* V) (e : R →+* V) (he : e.comp b₁ = b.comp b'') :
    ∃ (f' : pullback C''.s (spMap b) ⟶ C₀.X) (τ : SAB H (pullback C''.s (spMap b)))
      (n₁ : SABMap τ C''.t (pullback.fst _ _)) (n₂ : SABMap τ C₀.t f'),
      (∀ g : U'' ⟶ pullback C''.s (spMap b), g ≫ pullback.fst _ _ = C''.j → g ≫ f' = (r'' ≫ r) ≫ C₀.j) ∧
      ∀ y : t''.G.left ⟶ τ.G.left, y ≫ n₁.φ = C''.m.φ → y ≫ n₂.φ = (ν''.φ ≫ ν.φ) ≫ C₀.m.φ := by
  have w₀ : (pullback.fst C''.s (spMap b) ≫ A''.π) ≫ C'.s = (pullback.snd _ _ ≫ spMap e) ≫ spMap b₁ := by
    rw [Category.assoc, A''.π_over, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← spMap_comp, ← spMap_comp, he]
  let g₀ : pullback C''.s (spMap b) ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₀
  have hg₀ : g₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ A''.π := pullback.lift_fst _ _ _
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C''.s (spMap b)) C''.t
  obtain ⟨k₁, hk₁⟩ := LevelCover.sab_comp n₁ A''.mu rfl
  obtain ⟨k₂, hk₂⟩ := LevelCover.sab_cancel m₁ k₁ g₀ hg₀
  obtain ⟨k₃, hk₃⟩ := LevelCover.sab_comp m₂ A₁.mu rfl
  obtain ⟨n₂, hn₂⟩ := LevelCover.sab_comp k₂ k₃ rfl
  have w₁ : C'.j ≫ C'.s = (c ≫ spMap ω) ≫ spMap b₁ := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C'.jQ_over, Category.assoc, ← spMap_comp, hω]
  let g₁ : U ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₁
  have hg₁ : g₁ ≫ pullback.fst _ _ = C'.j := pullback.lift_fst _ _ _
  refine ⟨_, _, n₁, n₂, fun g hg => ?_, fun y hy => ?_⟩
  · have : g ≫ g₀ = r'' ≫ g₁ := by
      rw [← cancel_mono (pullback.fst C'.s (spMap b₁)), Category.assoc, hg₀, ← Category.assoc, hg, A''.j_comm,
        Category.assoc, hg₁]
    rw [← Category.assoc, this, Category.assoc, ← Category.assoc g₁, h₁ g₁ hg₁, A₁.j_comm, Category.assoc]
  · have p₁ : IsPullback m₁.φ t₁.G.hom C'.t.G.hom (pullback.fst C'.s (spMap b₁)) := m₁.cart.1
    have w₂ : C'.m.φ ≫ C'.t.G.hom = (t.G.hom ≫ g₁) ≫ pullback.fst C'.s (spMap b₁) := by
      rw [Category.assoc, hg₁]
      exact C'.m.cart.1.w
    have hy₁ : p₁.lift _ _ w₂ ≫ m₁.φ = C'.m.φ := p₁.lift_fst _ _ _
    have : Mono m₁.φ := (MorphismProperty.monomorphisms _).of_isPullback p₁.flip
      (inferInstanceAs (Mono (pullback.fst C'.s (spMap b₁))))
    have e₁ : y ≫ k₂.φ = ν''.φ ≫ p₁.lift _ _ w₂ := by
      rw [← cancel_mono m₁.φ, Category.assoc, hk₂, hk₁, ← Category.assoc, hy, A''.φ_comm, Category.assoc, hy₁]
    rw [hn₂, hk₃, ← Category.assoc, e₁, Category.assoc, ← Category.assoc _ m₂.φ, h₂ _ hy₁, A₁.φ_comm, Category.assoc]

theorem base_ring (l : Level H) (h : l.A = 1) {S : ℕ} (hS : 0 < S) :
    (∃ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S 1) ∧
      ∀ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  have := GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by simp [h])
  rwa [h] at this

theorem exists_global_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  intro hExt L₁ L₂ L₃ E _ _ _ H D Xo _ hN S l c hg hA
  let P := {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p}
  have : Finite P := finite_parts l
  have hP : ∀ x : P, x.1.A = 1 ∧ x.1.Dvd l := fun x => by
    obtain ⟨p, hp, h⟩ := x.2
    exact ⟨h.1, ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l x.1 h).1⟩
  have hcop : ∀ (p : ℕ), p.Prime → ∀ l₀ : Level H, IsPrimeToPart l₀ l p → (S.n (S.ch p) * l₀.M).Coprime p :=
    fun p hp l₀ h => Nat.Coprime.mul_left ((Nat.coprime_primes (S.aux _).1 hp).mpr (S.ch_ne p))
      ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l l₀ h).2.1
  have : Nonempty P := by
    obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H 2 Nat.prime_two).1 l (hg 2 Nat.prime_two)
    exact ⟨⟨l₀, 2, Nat.prime_two, h⟩⟩
  let a : Bool × P → ℕ := fun i => S.n i.1 * i.2.1.M
  have ha : ∀ i, 0 < a i := fun i => Nat.mul_pos (S.aux _).1.pos (lt_of_lt_of_le (by norm_num) i.2.1.three_le)
  let B : ∀ i : Bool × P, BaseModel (S.T i.1) i.2.1 := fun i => S.B i.1 i.2.1 (hP i.2).1
  choose k r ν hr hk hlev hfin _ using fun x : P => GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN x.1 l (hP x).2
  have hnorm : Geo.Tor.IsNormalScheme (Xo l).X := by
    have := (Xo l).smooth
    exact (GlobalTheory.isNormalScheme_iff_pred _).mp (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let ω : ∀ i : Bool × P, RZ H (a i) 1 →+* KA l := fun i => (k i.2).comp (B i).β
  have hω : ∀ i, IsInc (RZ H (a i) 1).subtype (KA l).val.toRingHom (ω i) := fun i x =>
    (hk i.2 _).trans ((B i).β_inc x)
  have hωd : ∀ i, IsDedFrac (ω i) := fun i => (base_ring l hA (ha i)).2.2 _ (hω i)
  choose C hC using fun i : Bool × P => GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ (B i).β _ _ _ (Xo l).s (Xo l).univ.t (ω i) (B i).C
    (RingHom.id _) (k i.2) (r i.2) (hr i.2) (ν i.2) ((base_ring i.2.1 (hP i.2).1 (ha i)).2.2 _ (B i).β_inc) (hωd i)
    rfl hnorm (hfin i.2)
  obtain ⟨⟨β₀, hβ₀⟩, hft, hd₀⟩ := base_ring l hA Nat.one_pos
  choose b₁ hb₁ using fun i : Bool × P => (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).1
  have hωb : ∀ i, (ω i).comp (b₁ i) = β₀ := fun i =>
    RingHom.ext fun x => Subtype.ext ((hω i _).trans ((hb₁ i x).trans (hβ₀ x).symm))
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_model_dominating_models_on_open_cover hExt E H _ _ _ (Xo l).s (Xo l).univ.t β₀ (Bool × P) (fun i => RZ H (a i) 1)
    (fun i => (a i : RZ H 1 1)) b₁ ω C (hd₀ _ hβ₀) (fun i => ⟨hωd i, hωb i, isLocalization_away (ha i) _ (hb₁ i)⟩)
    (span_natCast_eq_top a fun p hp => by
      obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).1 l (hg p hp)
      exact ⟨(S.ch p, ⟨l₀, p, hp, h⟩), (Nat.Prime.coprime_iff_not_dvd hp).mp (hcop p hp l₀ h).symm⟩)
    hft (Xo l).univ.proper
  obtain ⟨hdO, -, hbO, hV⟩ := GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H l c
  obtain ⟨b₀, hb₀⟩ := hbO 1 (one_dvd _)
  have hb₀' : (algebraMap (𝓞 c.F) c.F).comp b₀ = (IntermediateField.inclusion c.le).toRingHom.comp β₀ :=
    RingHom.ext fun x => Subtype.ext ((hb₀ x).trans ((hβ₀ x).symm.trans
      (IntermediateField.coe_inclusion c.le (β₀ x)).symm))
  obtain ⟨oF, ⟨m0⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) (Xo l).X ((Xo l).XF c)
    (Xo l).s (pullback.fst _ _ ≫ (Xo l).s) (pullback.fst _ _) rfl rfl
    (by rw [LevelCover.spMap_id', Category.comp_id]) (Xo l).univ
  have hnormF : Geo.Tor.IsNormalScheme ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isNormalScheme_iff_pred _).mp (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  obtain ⟨C'', ⟨A''⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ β₀ ((Xo l).XF c) _ _ (pullback.snd _ _) oF.t
    (algebraMap (𝓞 c.F) c.F) C' b₀ (IntermediateField.inclusion c.le).toRingHom (pullback.fst _ _) pullback.condition
    m0.toSABMap (hd₀ _ hβ₀) hdO hb₀' hnormF (by rw [pullback.lift_fst_snd]; infer_instance)
  let Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F) :=
    ⟨C''.X, C''.s, C''.normal, C''.proj, C''.flat, C''.jQ, C''.jQ_over, C''.jQ_open, C''.jQ_dense, C''.t, oF, m0,
      C''.m, C''.ab_gen⟩
  refine ⟨Y, GlobalTheory.T.model_finite_over_moduliModel_descends E H D l (Xo l) c _ _ Y _ β₀ C' b₀ A'' (hd₀ _ hβ₀) hdO hb₀', fun p W hp hW b hb => ?_⟩
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW ⟨l, c, hg p hp⟩
  let i : Bool × P := (S.ch p, ⟨l₀, p, hp, h⟩)
  obtain ⟨hdV, -, hbV⟩ := hV p W hp hW
  obtain ⟨e, he⟩ := hbV (a i) 1 (hcop p hp l₀ h) Nat.one_pos (hA ▸ c.le (baseKA l).ζ.2)
  obtain ⟨f, t₁, m₁, m₂, -, h₁, h₂⟩ := hC' i
  obtain ⟨A₁⟩ := hC i
  have := (((GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).2 _ (hb₁ i)).2 rfl).1
  obtain ⟨f', τ, n₁, n₂, e₁, e₂⟩ := exists_map_to_base A'' A₁ (b₁ i) (hωb i) f t₁ m₁ m₂ h₁ h₂ b e
    (RingHom.ext fun x => Subtype.ext (Subtype.ext ((he _).trans ((hb₁ i x).trans ((hb₀ x).symm.trans
      (congrArg Subtype.val (hb _)).symm)))))
  obtain ⟨ν', hν'⟩ := LevelCover.sab_comp m0.toSABMap (ν i.2) rfl
  refine GlobalTheory.T.model_dominated_of_map_to_baseModel L₁ L₂ L₃ E H D Xo _ _ _ l₀ l (B i) c _ _ _ _ Y _ b f' τ n₁ n₂ _ ν'
    ((IntermediateField.inclusion c.le).toRingHom.comp (k i.2)) hdO hdV (RingHom.ext hb) hR ⟨fun x => ?_, fun x => ?_⟩
    (fun x => (IntermediateField.coe_inclusion c.le _).trans (hk i.2 x)) ?_ e₁ (hν' ▸ e₂)
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.eta x), Category.assoc, (hlev i.2).1,
      Category.assoc]
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.etaA x), Category.assoc, (hlev i.2).2,
      Category.assoc]
  · rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp]

end GlobalTheory.GlobalModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_model_of_local_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  first | exact @GlobalTheory.GlobalModel.exists_global_model | exact GlobalTheory.GlobalModel.exists_global_model | (intros; apply GlobalTheory.GlobalModel.exists_global_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkIso

open PrimCocycle

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_axis {M M' : LB B.left} (hM : M.IsLB) (hM' : M'.IsLB) {T : Over S} (x y : T ⟶ B)
    (h : x = 1 ∨ y = 1) : ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (lift x y).left).Gen, t.IsGen := by
  have key : ∀ {N : LB B.left}, N.IsLB →
      ∃ u : LB.Gen (LB.LinComb N (fun I => (lift x y).left ≫ lamφ B I) lamε), u.IsGen := fun {N} hN => by
    obtain ⟨u, hu, -⟩ := exists_gen hN (φ := PEmpty.elim) (ε := PEmpty.elim)
      (φ' := fun I => (lift x y).left ≫ lamφ B I) (ε' := lamε) (fun U _ g => by
        refine (Fintype.prod_empty _).trans (Eq.symm ((prod_lam x y g).trans ?_))
        rcases h with rfl | rfl
        · rw [_root_.one_mul, mul_right_comm (g y.left), mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
        · rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]) (LB.oneGen N)
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm)
    exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := key hM
  obtain ⟨u', hu'⟩ := key hM'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ fun _ => rfl)
    (chartPullOut M' (lamφ B) lamε _ _ fun _ => rfl) (IsoDescent.lbIso_of_gens hM hM' _ _ _ _ u hu u' hu')
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

theorem exists_gen_tensor {L : LB A.left} {M M' : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (h' : LBIso L (M'.pull ψ.left)) :
    ∃ t : ((LB.div (abelian₂ B M') (abelian₂ B M)).pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen := by
  have e : ∀ I, lamφ A I ≫ ψ.left = (ψ ⊗ₘ ψ).left ≫ lamφ B I := fun I =>
    congrArg (fun q => q.left)
      ((psum_hom (MonoidHom.mk' (fun z : A ⊗ A ⟶ A => z ≫ ψ) fun a b => MonObj.mul_comp a b ψ) (x2 A) I.down).trans
        ((congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])).trans
          (psum_hom (preHom (ψ ⊗ₘ ψ)) (x2 B) I.down).symm))
  obtain ⟨v, hv⟩ := h
  obtain ⟨v', hv'⟩ := h'
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullOut M (lamφ B) lamε _ _ e) (chartPullOut M' (lamφ B) lamε _ _ e)
    (LBIso.trans (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hM' _ _)
      (iso_linComb ((isGen_iff v).1 hv) (lamφ A) lamε).symm (iso_linComb ((isGen_iff v').1 hv') (lamφ A) lamε))
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ _) w hw

end GlobalTheory.HkIso

namespace GlobalTheory

open HkIso HeckePoint

theorem exists_objMap_of_isIsog_of_kerSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  intro E _ _ _ H D l p S _ s o o₁ o₂ ψ₁ ψ₂ K hp hpM ⟨⟨hom₁, fin₁, et₁, sur₁, lin₁, bun₁⟩, lev₁⟩
    ⟨⟨hom₂, fin₂, et₂, sur₂, lin₂, bun₂⟩, lev₂⟩ ker₁ ker₂ hK
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab₁ := isAbelianScheme_of_proper o₁.t o₁.proper
  have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, homα, hα, uα⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S _ _ _ ψ₁ ψ₂ hab hab₁ inferInstance hom₁ fin₁ et₁ sur₁ hom₂
    fun k _ _ t x hx => (ker₂ k t x).2 ((ker₁ k t x).1 hx)
  obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S _ _ _ ψ₂ ψ₁ hab hab₂ inferInstance hom₂ fin₂ et₂ sur₂ hom₁
    fun k _ _ t x hx => (ker₁ k t x).2 ((ker₂ k t x).1 hx)
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have : Epi ψ₂.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₂ := Over.epi_of_epi_left ψ₂
  have : IsIso α := ⟨β, by rw [← cancel_epi ψ₁, reassoc_of% hα, hβ, Category.comp_id],
    by rw [← cancel_epi ψ₂, reassoc_of% hβ, hα, Category.comp_id]⟩
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos hp.pos 2)).map
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
    rwa [map_natCast] at this
  have i₀ : (lbPow o.t.PP.L (p ^ 2)).IsLB := DVR.linComb_isLB _ o.t.PP.isLB _ _
  have i₁ := pull_isLB o₁.t.PP.isLB (𝟙 _)
  have i₂ := pull_isLB o₂.t.PP.isLB α.left
  have hlam : LBIso (abelian₂ o₁.t.G (o₁.t.PP.L.pull (𝟙 _))) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S _ _ ψ₁ o₁.t.PP.L _ (p ^ 2) hab hab₁ o₁.t.PP.isLB o₁.ample
      (LB.isLB_div (DVR.linComb_isLB _ i₂ _ _) (DVR.linComb_isLB _ i₁ _ _)) hom₁ fin₁ et₁ sur₁ (pow_pos hp.pos 2) hunit
      (fun k _ _ t x hx => hK k t x ((ker₁ k t x).1 hx))
      (exists_gen_axis i₁ i₂ _ _ (Or.inl rfl)) (exists_gen_axis i₁ i₂ _ _ (Or.inr rfl))
      (exists_gen_tensor i₀ i₁ i₂ ψ₁
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by simp) bun₁)
        (LBIso.chartPull (chartPullId _) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun _ => by
          rw [Category.id_comp, ← Over.comp_left, hα]) bun₂))
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso globalFns_holds hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  first | exact @GlobalTheory.exists_objMap_of_isIsog_of_kerSet | exact GlobalTheory.exists_objMap_of_isIsog_of_kerSet | (intros; apply GlobalTheory.exists_objMap_of_isIsog_of_kerSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.EndBuild

theorem exists_endomorphism_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ i hden hfam hsm => ?_⟩
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hrep, hp⟩, -, hfib⟩ := hfam
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z.hom (spMap x) ⟶ Z.left) → Prop := fun K _ x f =>
    ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (φ : t.A.left ⟶ Z.left)
      (hφ : Fib (n ^ 2) M th sc x t φ), Good b Mat κ β v x t ∧
      f = hφ.1.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
  have hG : ∀ q ∈ objPrimes b Mat κ β v,
      ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ := by
    intro q hq
    obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t ht
    exact ⟨K, inferInstance, x, _, hx, inferInstance, s, t, φ, hφ, ht, rfl⟩
  obtain ⟨K₀, _, x₀, φ₀, hx₀, hG₀⟩ := hG q₀ hden.2
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d G
    hrep hrep hprop hprop hsm (by
      rintro K _ x f ⟨_, s, t, φ, ⟨hφ, ⟨σ, hE, hσ⟩, hb, hl⟩, ⟨hs, ht, -⟩, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t.A ⟶ t.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · rw [← spMap_comp] at hs
        subst hs
        exact fun p' q' f hf h => hQ K (x.comp β) t σ p' q' f ht hf hE h)
    (fun r hr => hden.1 r fun q hq hqp => hr q (hG q hq) hqp) K₀ x₀ φ₀ hG₀
  refine ⟨f, fun h => hf (by rw [← hx₀] at h; exact h), fun R' _ ρ hu Z' π hpb => ?_⟩
  obtain ⟨F₀, hF₀, hF⟩ := H R' ρ hu Z'.left π Z'.hom hpb.w
  refine ⟨Over.homMk (hpb.lift F₀ Z'.hom hF₀) (hpb.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ ht hφ hw
  have e := hF K (x.comp ρ) _ ⟨inferInstance, s, t, φ ≫ π, hφ, ht, rfl⟩ (hφ.1.isoPullback.inv ≫ φ)
    (by rw [Category.assoc, IsPullback.isoPullback_inv_fst])
  rw [Category.assoc, cancel_epi] at e
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, e]
    exact congrArg (φ ≫ ·) (hpb.lift_fst _ _ _)
  · rw [Category.assoc, Category.assoc, Over.w, hw, ← Category.assoc, Over.w]

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphisms_extend_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_endomorphism_near | exact GlobalTheory.ZM.NearBuild.exists_endomorphism_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_endomorphism_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdditionMorphismThetaFamilyNearGoodPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdditionMorphismThetaFamilyNearGoodPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.BuildAdd

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem exists_add_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.cutBy_graph_addition hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ hDen hFam hSm => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hPR, hp⟩, -, hfib⟩ := hFam
  obtain ⟨I₂, M₂, th₂, hPR₂, hseg⟩ :=
    GlobalTheory.SegreCoord.exists_segre_coordinates R (Ix g ((n ^ j) ^ 2)) I Z M th hPR
  have hP1 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR).2.1
  have hP2 := (GlobalTheory.ZM.projRep_projective_ample _ _ _ _ _ _ hPR₂).2.1
  have hS2 : Smooth (Z ⊗ Z).hom := by
    have := hSm
    rw [Over.tensorObj_hom]
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x φ => ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s)
      (ψ : t.A.left ⟶ Z.left) (e : (t.A ⊗ t.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)), IsIso e ∧
      Good b Mat κ β v x t ∧ Fib (n ^ 2) M th sc x t ψ ∧ IsSquare ψ (e ≫ pullback.fst _ _) ∧
      e ≫ pullback.snd _ _ = (t.A ⊗ t.A).hom ∧ e ≫ φ = (μ[t.A]).left ≫ ψ
  have mk : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o)
      (t : TObj g ((n ^ j) ^ 2) J b s) (ψ : t.A.left ⟶ Z.left), Good b Mat κ β v x t →
      Fib (n ^ 2) M th sc x t ψ → ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare ψ φ₂ → ∃ φ, G K x φ := by
    intro K _ _ x s t ψ hG hF φ₂ hsq
    have hpb := GlobalTheory.ZM.BuildAdd.isPullback_square hF.1 φ₂ hsq
    refine ⟨hpb.isoPullback.inv ≫ (μ[t.A]).left ≫ ψ, inferInstance, s, t, ψ, hpb.isoPullback.hom, inferInstance, hG, hF, ?_,
      hpb.isoPullback_hom_snd, by simp⟩
    rw [hpb.isoPullback_hom_fst]
    exact hsq
  have hGprop : ∀ (K : Type) [Field K] (x : R →+* K) (φ : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left), G K x φ →
      φ ≫ Z.hom = pullback.snd _ _ ≫ spMap x ∧
      CutBy (graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th φ) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (i : (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2)) =>
          x ((p h.1 i.1.1 * p h.2 i.1.2) * p (h.1 + h.2) i.2)) := by
    intro K _ x φ hφ
    obtain ⟨_, s, t, ψ, e, _, hG, hF, hsq, hsn, heφ⟩ := hφ
    have hw : ψ ≫ Z.hom = t.A.hom ≫ spMap x := hF.1.w
    refine ⟨?_, ?_⟩
    · rw [← cancel_epi e, reassoc_of% heφ, reassoc_of% hsn, hw, ← Category.assoc, Over.w]
    have hs : s = spMap (x.comp β) := hG.1.trans (spMap_comp x β).symm
    subst hs
    obtain ⟨-, ⟨σ, hEmb, hσ⟩, -, hlab⟩ := hF
    obtain ⟨N₂, t₂, hN₂, hseg₂, heq⟩ :=
      GlobalTheory.ZM.BuildAdd.graph_transport x Z M th M₂ th₂ hPR₂.1 hseg t.A ψ _ σ hσ e hsq hsn φ heφ
    rw [← heq]
    have hl : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      rw [hσ, ← Category.assoc, ← Over.comp_left, lift_snd, hlab h]
      have hx : (sc h).left ≫ Z.hom = spMap (RingHom.id R) := by
        rw [Over.w]
        simp [Out.baseOver, spMap]
      have hu := (hPR.2.1 R (RingHom.id R) (sc h).left (p h) hx (hp h)).1
      exact GlobalTheory.SegreCoord.secCoord_of_loc (GlobalTheory.SegreCoord.unimod_map hu x)
        ((GlobalTheory.SegreCoord.loc_of_secCoord (hp h)).baseChange x)
    have := hQ K (x.comp β) t σ (fun h a => x (p h a)) N₂ t₂ hN₂ hEmb hseg₂ hl
    simp only [map_mul]
    exact this
  have hDense : DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} := by
    intro f hf
    apply hDen.1 f
    intro q hq hqp
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    have hG : Good b Mat κ β v x t := ⟨rfl, hsh, hth⟩
    obtain ⟨ψ, hψ⟩ := hfib K x _ t hG
    obtain ⟨φ₂, hsq⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ.1.w
    obtain ⟨φ, hφ⟩ := mk K x _ t ψ hG hψ φ₂ hsq
    exact hf q ⟨K, inferInstance, x, φ, hker, hφ⟩ hqp
  obtain ⟨K₀, _, _, x₀, t₀, hker₀, hsh₀, hth₀⟩ := hDen.2
  have hG₀ : Good b Mat κ β v x₀ t₀ := ⟨rfl, hsh₀, hth₀⟩
  obtain ⟨ψ₀, hψ₀⟩ := hfib K₀ x₀ _ t₀ hG₀
  obtain ⟨φ₂₀, hsq₀⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hψ₀.1.w
  obtain ⟨φ₀, hφ₀⟩ := mk K₀ x₀ _ t₀ ψ₀ hG₀ hψ₀ φ₂₀ hsq₀
  obtain ⟨f, hf0, H⟩ := GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit R
    (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2)) (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2))
    (Z ⊗ Z) Z I₂ I M₂ M th₂ th (fun h i => p h.1 i.1 * p h.2 i.2) (fun h c => p (h.1 + h.2) c) Q d G
    hPR₂ hPR hP2 hP1 hS2 hGprop hDense K₀ x₀ φ₀ hφ₀
  refine ⟨f, fun hf => hf0 ?_, ?_⟩
  · rw [← hker₀] at hf
    exact RingHom.mem_ker.mp hf
  intro R' _ ρ hu Z' π hπ
  obtain ⟨π₂, hsqπ⟩ := GlobalTheory.ZM.BuildAdd.exists_isSquare hπ.w
  have hpbπ := GlobalTheory.ZM.BuildAdd.isPullback_square hπ π₂ hsqπ
  obtain ⟨F, hF, hU⟩ := H R' ρ hu (Z' ⊗ Z').left π₂ (Z' ⊗ Z').hom hpbπ.w
  refine ⟨Over.homMk (hπ.lift F (Z' ⊗ Z').hom hF) (hπ.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ hG hFib hφw φ₂ hsq
  have hpb1 : IsPullback φ t.A.hom Z'.hom (spMap x) := by
    refine IsPullback.of_right ?_ hφw hπ
    rw [← spMap_comp]
    exact hFib.1
  have hpb2 := GlobalTheory.ZM.BuildAdd.isPullback_square hpb1 φ₂ hsq
  have hsq' : IsSquare (φ ≫ π) (φ₂ ≫ π₂) := by
    constructor
    · rw [Category.assoc, hsqπ.1, reassoc_of% hsq.1]
    · rw [Category.assoc, hsqπ.2, reassoc_of% hsq.2]
  have hpb3 := GlobalTheory.ZM.BuildAdd.isPullback_square hFib.1 (φ₂ ≫ π₂) hsq'
  have hGφ : G K (x.comp ρ) (hpb3.isoPullback.inv ≫ (μ[t.A]).left ≫ φ ≫ π) :=
    ⟨inferInstance, s, t, φ ≫ π, hpb3.isoPullback.hom, inferInstance, hG, hFib,
      by rw [hpb3.isoPullback_hom_fst]; exact hsq', hpb3.isoPullback_hom_snd, by simp⟩
  have key := hU K (x.comp ρ) _ hGφ (hpb3.isoPullback.inv ≫ φ₂)
    (by rw [Category.assoc]; exact hpb3.isoPullback_inv_fst)
  rw [Category.assoc, cancel_epi] at key
  show φ₂ ≫ hπ.lift F (Z' ⊗ Z').hom hF = (μ[t.A]).left ≫ φ
  apply hπ.hom_ext
  · rw [Category.assoc, hπ.lift_fst, Category.assoc]
    exact key.symm
  · rw [Category.assoc, hπ.lift_snd, Category.assoc, hφw, ← Category.assoc, Over.w]
    exact hpb2.w

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdditionMorphismThetaFamilyNearGoodPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addition_morphism_thetaFamily_near_goodPrime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_add_near | exact GlobalTheory.ZM.NearBuild.exists_add_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_add_near <;> assumption)
end
end

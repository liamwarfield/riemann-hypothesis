module

public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GeZeroOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
open NumberField Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.PtTie

namespace GlobalTheory.LevelSplit

theorem splitsIn_level_prime : ∀ (D : D7) (i : Fin 2), SplitsIn D.host.E (D.host.g i) := fun D i =>
  GlobalTheory.HalfGen.factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.LevelSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem card_sigma_fibre {A B : Type} [Fintype A] (m : A → ℕ) (ty : A ≃ B) (s : A) :
    (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s).card = m s := by
  have h : (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s)
      = (Finset.univ : Finset (Fin (m s))).map (Function.Embedding.sigmaMk (β := fun s => Fin (m s)) s) := by
    ext ⟨a, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq, Finset.mem_map,
      Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem flag_of_numbering : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  intro C _ V d _ A _ m ty J _ X h
  have h1 : ∀ g s, X.rkF g (ty g s) = m g s := by
    intro g s
    unfold RowData.rkF
    simp only [h]
    convert card_sigma_fibre (m g) (ty g) s
  have h2 : ∀ g a, X.rkF g a = m g ((ty g).symm a) := by
    intro g a
    rw [← h1, Equiv.apply_symm_apply]
  refine ⟨h1, ⟨⟨fun g a c => ⟨(ty g).symm a, Fin.cast (h2 g a) c⟩, ?_, ?_⟩, fun g a c => ⟨rfl, rfl⟩⟩⟩
  · intro g a c c' hc
    exact Fin.cast_injective _ (eq_of_heq (Sigma.mk.inj hc).2)
  · intro g a c
    rw [h]
    exact Equiv.apply_symm_apply _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowDataStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_of_letterNumbering_rowData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  first | exact @GlobalTheory.flag_of_numbering | exact GlobalTheory.flag_of_numbering | (intros; apply GlobalTheory.flag_of_numbering <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasis
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatedDirections

theorem directions_typed_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (A : Type) [Fintype A] (tau : A → (E →+* ℂ)), (∀ s s', s ≠ s' → ∃ x : 𝓞 E, V.v (emA3 io ι (tau s) x - emA3 io ι (tau s') x) = 0) → (∀ s (x : Fin (Dw.mult (tau s))) i, V.Ge 0 (ι (chartUnitVectors C3 ⟨tau s, x⟩ i))) ∧ (∀ s (x : Fin (Dw.mult (tau s))) (a : 𝓞 E), linAct (Y.B.A.act a) (fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) = emA3 io ι (tau s) a • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) ∧ (∃ w : Fin (chD C3.ch) → (Σ s : A, Fin (Dw.mult (tau s))) → C, (∀ i q, V.Ge 0 (w i q)) ∧ ∀ q q' : (Σ s : A, Fin (Dw.mult (tau s))), ∑ i, ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i) * w i q' = if q = q' then 1 else 0) ∧ ∀ s (v : Fin (chD C3.ch) → C), (∀ a : 𝓞 E, linAct (Y.B.A.act a) v = emA3 io ι (tau s) a • v) → ∃ b : Fin (Dw.mult (tau s)) → C, v = ∑ x, b x • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i) := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY A _ tau hsep
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    GlobalTheory.LabelledDirections.ge_zero_of_isIntegral V
      (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (M a).mulVec (fun s => ι (chartUnitVectors C3 ℓ s)) =
      emA3 io ι ℓ.1 a • fun s => ι (chartUnitVectors C3 ℓ s) := by
    intro a ℓ
    funext i
    have h := congrArg ι (GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 C3.ch a ℓ i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul] at h
    refine Eq.trans ?_ h
    show ∑ j, M a i j * ι (chartUnitVectors C3 ℓ j) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp only [M, hY.act, MvPowerSeries.coeff_map]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x i
    rw [huv]
    exact hval _
  · intro s x a
    exact heig a ⟨tau s, x⟩
  · have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) A
      (fun a => Dw.mult (tau a)) (chD C3.ch) M (fun a x => emA3 io ι (tau a) x)
      (fun q i => ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i)) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨tau q.1, q.2⟩)
      hsep
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (tau a)
        obtain ⟨W, hW⟩ := GlobalTheory.LabelledDirections.exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        dsimp only
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    exact GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (tau a) v hv

end GlobalTheory.SeparatedDirections
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasisStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separatedEmbeddings_directions_typedBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (A : Type) [Fintype A] (tau : A → (E →+* ℂ)), (∀ s s', s ≠ s' → ∃ x : 𝓞 E, V.v (emA3 io ι (tau s) x - emA3 io ι (tau s') x) = 0) → (∀ s (x : Fin (Dw.mult (tau s))) i, V.Ge 0 (ι (chartUnitVectors C3 ⟨tau s, x⟩ i))) ∧ (∀ s (x : Fin (Dw.mult (tau s))) (a : 𝓞 E), linAct (Y.B.A.act a) (fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) = emA3 io ι (tau s) a • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) ∧ (∃ w : Fin (chD C3.ch) → (Σ s : A, Fin (Dw.mult (tau s))) → C, (∀ i q, V.Ge 0 (w i q)) ∧ ∀ q q' : (Σ s : A, Fin (Dw.mult (tau s))), ∑ i, ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i) * w i q' = if q = q' then 1 else 0) ∧ ∀ s (v : Fin (chD C3.ch) → C), (∀ a : 𝓞 E, linAct (Y.B.A.act a) v = emA3 io ι (tau s) a • v) → ∃ b : Fin (Dw.mult (tau s)) → C, v = ∑ x, b x • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i) := by
  first | exact @GlobalTheory.SeparatedDirections.directions_typed_basis | exact GlobalTheory.SeparatedDirections.directions_typed_basis | (intros; apply GlobalTheory.SeparatedDirections.directions_typed_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem exists_mulEquiv_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩


open scoped CategoryTheory.Obj in
theorem exists_mulEquiv_ptTieF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hxF
  letI := H.starRing
  subst hxF
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) ≫ (I.G.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (I.G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨eA, hA⟩ := exists_mulEquiv_of_isGrpPullback gpG (TFK (R := T.V) F)
  obtain ⟨e2, h2⟩ := exists_mulEquiv_of_isGrpPullback I.m2.cart (TFK (R := T.V) F)
  obtain ⟨e1, h1⟩ := exists_mulEquiv_of_isGrpPullback I.m1.cart (TFK (R := T.V) F)
  refine ⟨(eA.trans e2.symm).trans e1, fun x b => ⟨?_, ?_⟩, fun a x => ?_⟩
  · rintro ⟨r, hr, hr1, hr2⟩
    let r' : TFK (R := T.V) F ⟶ I.t'.G := Over.homMk r hr
    have h3 : e2 r' = eA x := Over.OverMorphism.ext (by
      rw [h2, hA]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc]))
    show b = e1 (e2.symm (eA x))
    rw [← h3, e2.symm_apply_apply]
    exact Over.OverMorphism.ext (hr1.symm.trans (h1 r').symm)
  · rintro rfl
    refine ⟨(e2.symm (eA x)).left, Over.w _, (h1 _).symm, ?_⟩
    refine (h2 _).symm.trans ?_
    rw [e2.apply_symm_apply, hA, Over.comp_left, Category.assoc]
  · have h3 : e2.symm (eA (x ≫ P.oA.act a)) = e2.symm (eA x) ≫ I.t'.act.act a := by
      rw [MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hA, h2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, actA, I.m2.act a,
        ← Category.assoc _ I.m2.cm.F, ← h2, e2.apply_symm_apply, hA, Category.assoc, Category.assoc]
    show e1 (e2.symm (eA (x ≫ P.oA.act a))) = e1 (e2.symm (eA x)) ≫ Xo.univ.t.act.act a
    rw [h3]
    apply Over.OverMorphism.ext
    rw [h1, Over.comp_left, Over.comp_left, h1, Category.assoc, Category.assoc, I.m1.act a]

end GlobalTheory.PtTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  first | exact @GlobalTheory.PtTie.exists_mulEquiv_ptTieF | exact GlobalTheory.PtTie.exists_mulEquiv_ptTieF | (intros; apply GlobalTheory.PtTie.exists_mulEquiv_ptTieF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlace
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceClosedField

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {x : 𝓞 K} (hx : x ∈ la.asIdeal) (h0 : x ≠ 0) : 0 < vLa la ((x : 𝓞 K) : K) := by
  have h1 : la.intValuation x < 1 := (la.intValuation_lt_one_iff_mem _).2 hx
  have h2 : WithZero.log (la.intValuation x) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  have h : ((x : 𝓞 K) : K) = algebraMap (𝓞 K) K x := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap]
  omega

theorem ramOverZ_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 := vLa_pos_of_mem la (Crude.crv_char_mem la) h0
  have h2 : ((((resCharOf la : ℕ) : 𝓞 K)) : K) = ((resCharOf la : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [h2, h] at h1
  exact_mod_cast h1

theorem vV_unit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem le_nval_mul (T : CDVR) {e r : ℕ} (hr : 0 < r) (ν : ℝ) (x : T.Fr)
    (h : (((r : ℝ) * ν : ℝ) : EReal) ≤ nval T.V e x) : (ν : EReal) ≤ nval T.V (e * r) x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero]; exact le_top
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Nat.cast_mul, ← div_div, le_div_iff₀ hr', mul_comm]
  exact h

theorem exists_closed_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  intro E _ _ _ H Dw lv Xo c _ la T io e ho
  have hp := Crude.resCharOf_prime la
  have hr := ramOverZ_pos la
  have he : 0 < e := ho.1
  have hv : vV T.V ((resCharOf la : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, Crude.crv_vLa_char]
  have hpos : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
  have hnu : ¬ IsUnit ((resCharOf la : ℕ) : T.V) := by
    intro hu
    have h0 := vV_unit T hu
    rw [map_natCast, hv] at h0
    omega
  obtain ⟨C, _, _, v, ι, h1, h2, h3, h4⟩ :=
    GlobalTheory.DvrClosedEmbedding.exists_complete_isAlgClosed_addValuation T _ hp hnu
  refine ⟨C, inferInstance, inferInstance, ⟨v, resCharOf la, hp, h1⟩, ι, rfl, h2, h3, h4, ?_, ?_, ?_⟩
  · intro x hx
    show (0 : WithTop ℝ) < v _
    by_cases h0 : x = 0
    · subst h0; simp
    have hx0 : ((x : 𝓞 c.F) : c.F) ≠ 0 := by simpa using h0
    rw [h2 _ ((map_ne_zero io).2 hx0), ho.2, hv]
    have := vLa_pos_of_mem la hx h0
    have h5 : (0 : ℝ) < (((e : ℤ) * vLa la ((x : 𝓞 c.F) : c.F) : ℤ) : ℝ) / (((e : ℤ) * (ramOverZ la : ℤ) : ℤ) : ℝ) := by
      apply div_pos
      · exact_mod_cast mul_pos (by exact_mod_cast he) this
      · exact_mod_cast hpos
    exact_mod_cast h5
  · intro m hm
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    have hm1 : ((m : ℕ) : c.F) ≠ 0 := by exact_mod_cast hm0
    show v (m : C) = 0
    rw [← map_natCast ι, ← map_natCast io, h2 _ ((map_ne_zero io).2 hm1), ho.2, Crude.crv_vLa_coprime la hm]
    simp
  · intro y C3 k a n ν h
    have hE : eOf T (⟨v, resCharOf la, hp, h1⟩ : VF C) = e * ramOverZ la := by
      show (vV T.V ((resCharOf la : ℕ) : T.Fr)).toNat = _
      rw [hv, ← Nat.cast_mul, Int.toNat_natCast]
    rw [hE]
    unfold nuLocC at h ⊢
    simp only [le_iInf_iff] at h ⊢
    intro P hP f hf
    exact le_nval_mul T hr ν _ (h P hP f hf)

end GlobalTheory.PlaceClosedField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlaceStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedComplete_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  first | exact @GlobalTheory.PlaceClosedField.exists_closed_field_over_place | exact GlobalTheory.PlaceClosedField.exists_closed_field_over_place | (intros; apply GlobalTheory.PlaceClosedField.exists_closed_field_over_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.UnrIdem

theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add (f := _)]; exact mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end GlobalTheory.UnrIdem

open GlobalTheory.UnrIdem in
theorem GlobalTheory.exists_idempotent_of_unramified_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using UnrIdem.mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramifiedStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  first | exact @GlobalTheory.exists_idempotent_of_unramified_place | exact GlobalTheory.exists_idempotent_of_unramified_place | (intros; apply GlobalTheory.exists_idempotent_of_unramified_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertLabelling

open GlobalTheory.LevelsOrbits

lemma ordP_dvd_of_pos_eq (N : NumDatum) (l : ℕ) (z : RPl N.R) (u : ℕ) (h : N.pos l z u = z) : N.ordP l ∣ u := by
  unfold NumDatum.pos at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have h3 : u • N.hP l = 0 := by simpa using h2
  unfold NumDatum.ordP
  by_cases hc : N.cls l = PrimeClass.signal
  · rw [if_pos hc]
    have ho : ¬ Odd u := by
      intro ho
      rw [decide_eq_true (⟨hc, ho⟩ : N.cls l = PrimeClass.signal ∧ Odd u)] at h1
      cases hz : z.1 <;> simp [hz] at h1
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.1 ho
    rw [← two_mul]
    refine Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero ?_)
    rw [← mul_smul, mul_two, h3]
  · rw [if_neg hc]
    exact addOrderOf_dvd_of_nsmul_eq_zero h3

lemma pos_inj (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ZMod (N.ordP l))
    (h : N.pos l z s.val = N.pos l z t.val) : s = t := by
  wlog hst : s.val ≤ t.val generalizing s t
  · exact (this t s h.symm (not_le.1 hst).le).symm
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hst
  rw [hu, ← pos_add] at h
  have hd := ordP_dvd_of_pos_eq N l _ u h.symm
  have hlt := ZMod.val_lt t
  have : u = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  apply ZMod.val_injective
  omega

def orbSetoid (N : NumDatum) (l : ℕ) : Setoid (RPl N.R) where
  r z z' := ∃ s : ℕ, N.pos l z s = z'
  iseqv := ⟨fun z => ⟨N.ordP l * 0, pos_mul_period N l z 0⟩, fun {z z'} ⟨s, hs⟩ => ⟨(N.ordP l - 1) * s, by
      have hp : 0 < N.ordP l := Nat.pos_of_ne_zero (NeZero.ne _)
      obtain ⟨n, hn⟩ : ∃ n, N.ordP l = n + 1 := ⟨N.ordP l - 1, by omega⟩
      rw [← hs, pos_add, show s + (N.ordP l - 1) * s = N.ordP l * s by rw [hn, Nat.add_sub_cancel]; ring,
        pos_mul_period]⟩,
    fun {a b c} ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s + t, by rw [← pos_add, hs, ht]⟩⟩

lemma exists_reps (N : NumDatum) (l : ℕ) : ∃ Z : Finset (RPl N.R),
    ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z' := by
  refine ⟨Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : (orbSetoid N l).r (Quotient.mk (orbSetoid N l) z').out z' := Quotient.mk_out z'
  have key : ∀ p : RPl N.R × ZMod (N.ordP l),
      p.1 ∈ (Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z) ∧ N.pos l p.1 p.2.val = z' →
      p.1 = (Quotient.mk (orbSetoid N l) z').out := by
    rintro p ⟨h1, h2⟩
    rw [← (Finset.mem_filter.1 h1).2]
    congr 1
    exact Quotient.sound ⟨_, h2⟩
  refine ⟨((Quotient.mk (orbSetoid N l) z').out, (s : ZMod (N.ordP l))), ⟨?_, ?_⟩, fun p hp => ?_⟩
  · simp
  · rw [ZMod.val_natCast, pos_mod, hs]
  · have h1 := key p hp
    refine Prod.ext h1 (pos_inj N l p.1 _ _ ?_)
    rw [hp.2, ZMod.val_natCast, pos_mod, h1, hs]

lemma even_ordP (N : NumDatum) (l : ℕ) (hI : Inert N l) (hC : ¬ ConjIn N l) : Even (N.ordP l) :=
  GlobalTheory.GoodDepth.even_ordP_of_not_conjIn hI hC

lemma bg_succ {d : ℕ} [NeZero d] (hd : Even d) (s : ZMod d) (g : Fin 2) : g = RF.bg (s + 1) ↔ ¬ g = RF.bg s := by
  have h : Even (s + 1).val ↔ ¬ Even s.val := by
    have e : s + 1 = ((s.val + 1 : ℕ) : ZMod d) := by simp
    rw [e, ZMod.val_natCast, ← Nat.even_add_one, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hd)]
  unfold RF.bg
  by_cases hs : Even s.val
  · rw [if_pos hs, if_neg (fun hh => h.1 hh hs)]; fin_cases g <;> simp
  · rw [if_neg hs, if_pos (h.2 hs)]; fin_cases g <;> simp

lemma pos_succ (N : NumDatum) (l : ℕ) (z : RPl N.R) (s : ZMod (N.ordP l)) :
    N.pos l z (s + 1).val = N.pos l (N.pos l z s.val) 1 := by
  have e : s + 1 = ((s.val + 1 : ℕ) : ZMod (N.ordP l)) := by simp
  rw [e, ZMod.val_natCast, pos_mod, pos_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

lemma inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by linear_combination this)
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, this, map_neg, map_natCast]
  have h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w := by
    intro w hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two] at hre him
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : w.re = 0 := by
      by_contra hne
      have : w.im = 0 := by
        have : w.re * w.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [this]
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h2 _ h1]
  have h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)
  constructor
  · intro a b
    exact h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)
  · intro a
    rw [h3.resolve_left a, neg_neg]

lemma embK_conj_bar {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c (ComplexEmbedding.conjugate τ) x := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

lemma conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  intro E _ _ _ H lv c N pl hT la T io C _ _ V ι _ hl hla hI hC j
  obtain ⟨Z, hZ⟩ := exists_reps N V.l
  have hev := even_ordP N V.l hI hC
  have hin : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  have hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')
  have hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    (ComplexEmbedding.involutive_conjugate E).injective
  refine ⟨Z, hZ, ?_, hev, ⟨?_, ?_⟩, fun z g => ⟨fun s x => ?_, fun s => ?_⟩⟩
  · obtain ⟨p, hp, -⟩ := hZ (false, 0)
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    have main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (g = RF.bg s ↔ g' = RF.bg s') →
        (z, g, s) = (z', g', s') := by
      intro h1 h2
      have := (hZ _).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, h1⟩ ⟨z'.2, rfl⟩
      obtain ⟨a, b⟩ := Prod.mk.inj this
      obtain rfl := Subtype.ext a
      subst b
      have : g = g' := (by decide : ∀ g g' b : Fin 2, (g = b ↔ g' = b) → g = g') _ _ _ h2
      rw [this]
    dsimp only [tauIn] at h
    by_cases a : g = RF.bg s <;> by_cases b : g' = RF.bg s'
    · rw [if_pos a, if_pos b] at h
      exact main (hT.inj h) (by tauto)
    · rw [if_pos a, if_neg b] at h
      exact absurd h (hne _ _)
    · rw [if_neg a, if_pos b] at h
      exact absurd h.symm (hne _ _)
    · rw [if_neg a, if_neg b] at h
      exact main (hT.inj (hcinj h)) (by tauto)
  · intro τ
    by_cases h : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hT.psi _).1 h
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg p.2, p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_pos rfl, hp.2]
    · obtain ⟨z', hz'⟩ := (hT.psi _).1 ((inPsi_conj_iff τ).2 h)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg (p.2 + 1), p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_neg ((bg_succ hev _ _).1 rfl), hp.2, hz', conj_conj]
  · have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
        emA3 io ι (pl w) x ^ V.l) := by
      intro w x
      obtain ⟨y, hy, e⟩ := hT.frob la (hl ▸ hI) w x
      have := hla y hy
      rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
      exact this
    unfold tauIn
    rw [pos_succ]
    by_cases a : g = RF.bg s
    · rw [if_pos a, if_neg (fun hh => (bg_succ hev _ _).1 hh a)]
      exact hf _ _
    · rw [if_neg a, if_pos ((bg_succ hev _ _).2 a)]
      have := hf (N.pos V.l z s.val) (H.bar x)
      simp only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢
      exact this
  · unfold tauIn
    by_cases a : (0 : Fin 2) = RF.bg s
    · rw [if_pos a, if_neg (by rw [← a]; decide)]
    · rw [if_neg a, if_pos (by revert a; generalize RF.bg s = b; revert b; decide), conj_conj]

end GlobalTheory.InertLabelling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConjStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  exact @GlobalTheory.InertLabelling.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximal
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeriesFrobRoot

theorem eq_pow_of_pderiv {k σ : Type} [CommRing k] [IsDomain k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (b c : MvPowerSeries σ k) (hb : ∀ i, MvPowerSeries.pderiv (R := k) i b = 0)
    (hc : ∀ ν, MvPowerSeries.coeff ν c ^ p = MvPowerSeries.coeff (p • ν) b) : b = c ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext μ
  rw [MvPowerSeries.coeff_map]
  by_cases h : ∀ i, p ∣ μ i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = μ := ⟨μ.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, frobenius_def, hc]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have h0 : μ i ≠ 0 := fun h => hi (h ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (μ - Finsupp.single i 1)) (hb i)
    rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle, map_zero] at h1
    refine (mul_eq_zero.1 h1).resolve_right fun h2 => hi ?_
    rw [← CharP.cast_eq_zero_iff k p]
    have h3 : μ i = ((μ - Finsupp.single i 1 : σ →₀ ℕ) i) + 1 := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    rw [h3]; push_cast; exact h2

variable {C : Type} [Field C] {V : VF C} {σ : Type}

open TeichPair

theorem exists_lift {f : MvPowerSeries σ C} (hf : IntS V f) :
    ∃ F : MvPowerSeries σ (intRing V), MvPowerSeries.map (intRing V).subtype F = f :=
  ⟨fun μ => ⟨MvPowerSeries.coeff μ f, hf μ⟩, by ext μ; rfl⟩

theorem mm_iff (F : MvPowerSeries σ (intRing V)) :
    (∀ μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.map (intRing V).subtype F))) ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maxId V)) F = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun μ => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem charP_res (V : VF C) : CharP (intRing V ⧸ maxId V) V.l := by
  refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]
  show 0 < V.v (((V.l : ℕ) : intRing V) : C)
  rw [show (((V.l : ℕ) : intRing V) : C) = (V.l : C) by simp, V.v_l]
  exact zero_lt_one

theorem pderiv_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    MvPowerSeries.pderiv (R := S) i (MvPowerSeries.map φ F) = MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) i F) := by
  ext μ
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]

theorem ge_of_pow {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  by_contra hx
  rw [not_le] at hx
  induction hv : V.v x using WithTop.recTopCoe with
  | top => rw [hv] at hx; exact not_top_lt hx
  | coe t =>
    rw [hv] at hx h
    rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [WithTop.coe_lt_coe] at hx
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith

theorem main : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  intro C _ _ V σ _
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  have := charP_res V
  have : CharP (MvPowerSeries σ (intRing V ⧸ maxId V)) V.l :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ)) V.l
  have : IsDomain (MvPowerSeries σ (intRing V ⧸ maxId V)) := NoZeroDivisors.to_isDomain _
  refine ⟨fun b hb hd => ?_, fun f g hf hg h => ?_, fun f g hf hg => ?_⟩
  · choose r hr using fun ν : σ →₀ ℕ =>
      IsAlgClosed.exists_pow_nat_eq (MvPowerSeries.coeff (V.l • ν) b) V.l_prime.pos
    have hri : ∀ ν, V.Ge 0 (r ν) := fun ν => ge_of_pow V.l_prime.ne_zero (by rw [hr]; exact hb _)
    obtain ⟨B, rfl⟩ := exists_lift hb
    let B' : MvPowerSeries σ (intRing V) := fun ν => ⟨r ν, hri ν⟩
    refine ⟨MvPowerSeries.map (intRing V).subtype B', hri, ?_⟩
    rw [← map_pow, ← map_sub, mm_iff, map_sub, map_pow, sub_eq_zero]
    refine eq_pow_of_pderiv V.l _ _ (fun i => ?_) fun ν => ?_
    · rw [pderiv_map', ← mm_iff, ← pderiv_map']
      exact hd i
    · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← map_pow]
      congr 1
      exact Subtype.ext (hr ν)
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [← map_pow, ← map_pow, ← map_sub, mm_iff, map_sub, map_pow, map_pow, ← sub_pow_char] at h
    rw [← map_sub, mm_iff, map_sub]
    exact (pow_eq_zero_iff V.l_prime.ne_zero).1 h
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [forall_and]
    constructor
    · rw [← map_add (f := _), ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, map_add (f := _), add_pow_char]
      ring
    · rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, sub_pow_char]
      ring

end GlobalTheory.SeriesFrobRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximalStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  first | exact @GlobalTheory.SeriesFrobRoot.main | exact GlobalTheory.SeriesFrobRoot.main | (intros; apply GlobalTheory.SeriesFrobRoot.main <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.HarmCopies

open GlobalTheory.PowGerm

theorem monomial_eq_boxSer {k : Type} [CommRing k] {n d : ℕ} (e : Fin n × Fin d →₀ ℕ) :
    (MvPowerSeries.monomial e 1 : PS k n d) =
      boxSer fun b => ∏ j : Fin d, (MvPowerSeries.X ((0 : Fin 1), j) : PS k 1 d) ^ e (b, j) := by
  unfold boxSer
  simp only [map_prod, map_pow, MvPowerSeries.rename_X]
  rw [← Fintype.prod_prod_type' (fun b j => (MvPowerSeries.X (b, j) : PS k n d) ^ e (b, j)),
    MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem exists_jet {k : Type} [CommRing k] {n d : ℕ} (N : ℕ) (f : PS k n d) :
    ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N →
      MvPowerSeries.coeff e f =
        MvPowerSeries.coeff e (∑ j : S, MvPowerSeries.coeff j.1 f • (MvPowerSeries.monomial j.1 1 : PS k n d)) := by
  classical
  refine ⟨(Finsupp.finite_of_degree_le N).toFinset, fun e he => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single ⟨e, by simpa using he⟩]
  · simp
  · intro j _ hj
    rw [map_smul, MvPowerSeries.coeff_monomial_ne (fun h => hj (Subtype.ext h.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def letterEquiv (T : Type) (r : T → ℕ) (n : ℕ) : (Σ τ : T, Fin (r τ)) × Fin n ≃ Formalism.L2.Pj.Letter T r n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem const_eq_zero {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} (hh : B.IsCanonGauge k h) :
    MvPowerSeries.constantCoeff h = 0 := by
  rw [← TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt (n := 1) 0)) h, hh.ax0, map_zero]

theorem col_sum_eq_zero {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : MvPolynomial.rename (letterEquiv T r n) Q ∈ harmK r n k cc isX (fun _ => 1))
    (τ : T) (hτ : isX τ) (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
      (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hQ
  have h := hQ τ hτ i i'
  apply MvPolynomial.rename_injective _ (letterEquiv T r n).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← h, map_sum, lap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, one_smul, ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective,
      ← MvPolynomial.pderiv_rename (letterEquiv T r n).injective]
    rfl
  · intro b' _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul, LinearMap.zero_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.HarmCopies

namespace GlobalTheory


open HarmCopies PowGerm in
theorem nabValN_harmonic_gauge_independent :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n P hP w0 q f
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv T r n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv T r n).surjective P
  obtain ⟨S, hS⟩ := exists_jet (MvPolynomial.rename (letterEquiv T r n) Q).totalDegree f
  rw [(nabJet R d O B k h w0 q n _ _ _).1 _ _ _ hS, (nabJet R d O B k h' w0 q n _ _ _).1 _ _ _ hS,
    (nabJet R d O B k h w0 q n _ _ _).2.1, (nabJet R d O B k h' w0 q n _ _ _).2.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [monomial_eq_boxSer,
    nabValN_boxSer R d O B k h w0 (const_eq_zero hh) q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl),
    nabValN_boxSer R d O B k h' w0 (const_eq_zero hh') q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl)]
  exact canonGauge_independence_harmonic R d O k B h h' hh hh' T r cc isX σ hcc hX hσ hsep u hu n Q
    (col_sum_eq_zero Q hP) w0 q _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValueCopies_gauge_independent : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  first | exact @GlobalTheory.nabValN_harmonic_gauge_independent | exact GlobalTheory.nabValN_harmonic_gauge_independent | (intros; apply GlobalTheory.nabValN_harmonic_gauge_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory.ChartCmp.FrameRatio

theorem exists_corr_scaled {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ φ' : K → (Y ⟶ X)) (h : φ = φ') (ε : K → ℤ) (g : LB.Gen (LB.LinComb L φ ε))
    (g' : LB.Gen (LB.LinComb L φ' ε)) (hg : g.IsGen) (hg' : g'.IsGen) :
    ∃ U : Γ(Y, ⊤)ˣ, LB.Gen.Corr L φ ε φ' ε g
      (⟨fun j => res le_top U * g'.s j⟩ : LB.Gen (LB.LinComb L φ' ε)) := by
  subst h
  obtain ⟨U, hU⟩ := GaugeR.ratio_of_gen L hL φ ε g' g hg' hg
  refine ⟨U, fun j j' _ _ hx => ?_⟩
  obtain rfl : j = j' := funext fun k => hx k k rfl
  rw [hU j]

theorem comp_psum' {S : Scheme.{0}} (G : Over S) [GrpObj G] {T T' : Over S} (f : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) : f ≫ psum G x I = psum G (fun k => f ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    simp only [List.foldr_cons, padd]
    rw [← Category.assoc, comp_lift]
    congr 2

theorem unitΓ_surj {A : Type} [CommRing A] (U : Γ(Sp A, ⊤)ˣ) : ∃ u : Aˣ, unitΓ u = U := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom U, Units.ext ?_⟩
  simp [unitΓ, toΓ]

theorem psJet_surj {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (a : Jet R κ m) :
    ∃ f : MvPowerSeries κ R, psJet m f = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨(p : MvPowerSeries κ R), GaugeR.psJet_eq_mk m _ p fun e _ => (MvPolynomial.coeff_coe p e).symm⟩

theorem copy_subst {V : Type} [CommRing V] (d m : ℕ) (φ : Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) (i : Fin 2)
    (hψ : ∀ j, ψ i j = psIn d m ![i] (φ j)) :
    (jetCopy d m i).comp (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) =
      (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2).comp (jetCopy d m i) := by
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, GaugeR.jetMap_mk, MvPolynomial.aeval_X, hψ, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  congr 2
  generalize psTrunc m (φ j) = P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    obtain ⟨a, b⟩ := k
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  intro E _ _ _ H V _ t d x x' e e' φ _ hc he he' m
  let ψ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V :=
    ![fun j => psIn d m ![0] (φ j), fun j => psIn d m ![1] (φ j)]
  have hpt : ∀ i : Fin 2, (∀ j, ψ i j = psIn d m ![i] (φ j)) → jptG t (𝟙 (Sp V)) d x' m i =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2) ≫ jptG t (𝟙 (Sp V)) d x m i := by
    intro i hi
    rw [jptG, jptG, hc m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp,
      copy_subst d m φ ψ i hi]
  have hfam : cφG t ![jptG t (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => ψ p.1 p.2)).left ≫
        cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, comp_psum']
    congr 2
    funext k
    fin_cases k
    · exact hpt 0 fun _ => rfl
    · exact hpt 1 fun _ => rfl
  obtain ⟨U, hU⟩ := exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (peG t (𝟙 (Sp V)) d x e m ψ) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := unitΓ_surj U
  obtain ⟨ε, hε⟩ := psJet_surj m (u : Jet V (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, u, hε.symm, hU⟩
  rw [← GaugeR.jetAug_psJet m ε, hε]
  exact u.isUnit.map _

end GlobalTheory.ChartCmp.FrameRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrderStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetFrames_differ_by_unit_each_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ : Pt V 1 d), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → ∀ m, ∃ ε : PS V 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧ FrRel t x x' e e' φ m ε := by
  first | exact @GlobalTheory.ChartCmp.FrameRatio.main | exact GlobalTheory.ChartCmp.FrameRatio.main | (intros; apply GlobalTheory.ChartCmp.FrameRatio.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.JCalc

variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

theorem jeq_refl (f : MvPowerSeries σ R) : JEq m f f := fun _ _ => rfl

theorem jeq_add {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f + g) (f' + g') :=
  fun e he => by rw [map_add (f := _), map_add (f := _), h e he, k e he]

theorem jeq_sub {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f - g) (f' - g') :=
  fun e he => by rw [map_sub, map_sub, h e he, k e he]

theorem jeq_mul {f f' g g' : MvPowerSeries σ R} (h : JEq m f f') (k : JEq m g g') : JEq m (f * g) (f' * g') := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
  rw [map_add (f := _)] at hsum
  rw [h p.1 (by omega), k p.2 (by omega)]

theorem jeq_cancel {f g u : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff u))
    (h : JEq m (f * u) (g * u)) : JEq m f g := by
  obtain ⟨c, hc⟩ := hu
  have h1 := MvPowerSeries.mul_invOfUnit u c hc.symm
  have := jeq_mul h (jeq_refl (MvPowerSeries.invOfUnit u c))
  rwa [_root_.mul_assoc, _root_.mul_assoc, h1, _root_.mul_one, _root_.mul_one] at this

theorem jeq_map {R' : Type} [CommRing R'] (β : R →+* R') {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) :=
  fun e he => by rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

theorem jeq_iff_truncTotal [Finite σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ MvPowerSeries.truncTotal (m + 1) f = MvPowerSeries.truncTotal (m + 1) g := by
  constructor
  · intro h
    ext e
    by_cases he : e.degree ≤ m
    · rw [MvPowerSeries.coeff_truncTotal _ (by omega), MvPowerSeries.coeff_truncTotal _ (by omega), h e he]
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega), MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]
  · intro h e he
    rw [← MvPowerSeries.coeff_truncTotal (n := m + 1) f (by omega),
      ← MvPowerSeries.coeff_truncTotal (n := m + 1) g (by omega), h]

theorem jeq_subst [Finite σ] {τ : Type} [Finite τ] {a a' : σ → MvPowerSeries τ R} {f g : MvPowerSeries σ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, JEq m (a i) (a' i)) (k : JEq m f g) :
    JEq m (MvPowerSeries.subst a f) (MvPowerSeries.subst a' g) := by
  rw [jeq_iff_truncTotal] at k ⊢
  simp only [jeq_iff_truncTotal] at h
  rw [MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha', k]
  simp only [h]

theorem jet_mk_eq_zero_iff (p : MvPolynomial σ R) :
    (Ideal.Quotient.mk _ p : Jet R σ m) = 0 ↔ ∀ e : σ →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  have h : orig R σ = MvPolynomial.idealOfVars σ R := rfl
  rw [Ideal.Quotient.eq_zero_iff_mem, h, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]

theorem mem_degLE_iff [Fintype σ] [DecidableEq σ] (e : σ →₀ ℕ) : e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter]
  have hd : (e.sum fun _ k => k) = e.degree := rfl
  rw [hd]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  refine Finset.mem_image.2 ⟨fun i => ⟨e i, Nat.lt_succ_of_le ((Finsupp.le_degree i e).trans h)⟩,
    Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem coeff_psTrunc_ite [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE_iff]

theorem jeq_iff_psJet [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R) :
    JEq m f g ↔ psJet m f = psJet m g := by
  rw [← sub_eq_zero (a := psJet m f), psJet, psJet, ← map_sub, jet_mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [MvPolynomial.coeff_sub, coeff_psTrunc_ite, coeff_psTrunc_ite, if_pos he, if_pos he, sub_eq_zero]

theorem eq_of_jeq {f g : MvPowerSeries σ R} (h : ∀ m', JEq m' f g) : f = g :=
  MvPowerSeries.ext fun e => h _ e le_rfl

theorem jeq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) :=
  fun _ _ _ =>
  ⟨fun _ _ _ _ _ h k => ⟨jeq_add h k, jeq_sub h k, jeq_mul h k⟩,
    fun _ _ _ _ hu h => jeq_cancel hu h,
    fun _ _ _ β _ _ h => jeq_map β h,
    fun _ _ _ _ _ _ _ ha ha' h k => jeq_subst (fun p => ha p.1 p.2) (fun p => ha' p.1 p.2) (fun p => h p.1 p.2) k,
    fun _ _ _ f g => jeq_iff_psJet f g,
    fun _ _ _ h => eq_of_jeq h⟩

end GlobalTheory.ChartCmp.JCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesJetEq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) := by
  first | exact @GlobalTheory.ChartCmp.JCalc.jeq_calculus | exact GlobalTheory.ChartCmp.JCalc.jeq_calculus | (intros; apply GlobalTheory.ChartCmp.JCalc.jeq_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ModelSquareFunctions

theorem isProper_genericFibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
  have h1 := I.m1.cart.1
  have h2 := I.m2.cart.1
  have hp : IsProper I.t'.G.hom := MorphismProperty.of_isPullback h1 Xo.univ.proper
  show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V (FractionRing T.V))))
  rw [← h2.isoPullback_inv_snd]
  infer_instance

theorem surjective_appTop_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  intro E _ _ _ H Dw l Xo c T io y I
  have h := (globalFnsDvr_of_globalFns GlobalTheory.globalFns_holds E H T.V T.cpl I.G (isProper_genericFibre I) 2).2
  let e : powObj I.G.G 2 ≅ I.G.G ⊗ I.G.G := I.G.G ◁ᵢ (ρ_ I.G.G)
  have hw : e.inv.left ≫ (powObj I.G.G 2).hom = (I.G.G ⊗ I.G.G).hom := Over.w e.inv
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (e.inv.left.app ⊤))
  rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso e.inv.left.appTop).2.comp h

end GlobalTheory.ModelSquareFunctions
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_appTop_integralModel_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  first | exact @GlobalTheory.ModelSquareFunctions.surjective_appTop_square | exact GlobalTheory.ModelSquareFunctions.surjective_appTop_square | (intros; apply GlobalTheory.ModelSquareFunctions.surjective_appTop_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

theorem GlobalTheory.units_cancel_first_law {U : Type} [CommGroup U] (g p q r abc ab ac bc a b c o : U) :
    g * ((abc * ab⁻¹ * c⁻¹ * o * p) * ((ac * a⁻¹ * c⁻¹ * o * q)⁻¹ * (bc * b⁻¹ * c⁻¹ * o * r)⁻¹)) =
      (abc * ab⁻¹ * ac⁻¹ * bc⁻¹ * a * b * c * o⁻¹) * (g * (p * (q⁻¹ * r⁻¹))) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.FramePartialLawTwo in
theorem GlobalTheory.frame_first_partial_law_iff_pullback :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph1 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx hθ e e' _ _ he F ph1 hF law
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  obtain ⟨c₁, h₁, h₂⟩ := he m
  refine corr_iff_of_val t.PP.isLB t'.PP.isLB fun y J J' hJ hJ' => ?_
  have eθ := val_cubic hθ (jptG t x0 d x m (0 : Fin 3)) (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jpt_push hx m 0) (jpt_push hx m 1) (jpt_push hx m 2) hJ hJ'
  have eA := val_frame h₁ h₂ ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_law t' _ d x' m F hF (law m) ![0, 1]) (subst_X t' _ d x' m 2) hJ hJ'
  have eB := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 2) hJ hJ'
  have eC := val_frame h₁ h₂ ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 1) (subst_X t' _ d x' m 2) hJ hJ'
  refine ⟨_, eθ, ?_⟩
  refine ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) eA ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) eB))
      ((val_inv _ _).trans (congrArg (·⁻¹) eC)))))))).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl ((GermB.val_scale t' _ _ _ _ _ _ _ hJ').trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  exact GlobalTheory.units_cancel_first_law _ _ _ _ _ _ _ _ _ _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameFirstPartialLawIffPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_firstPartialLaw_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph1 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  first | exact @GlobalTheory.frame_first_partial_law_iff_pullback | exact GlobalTheory.frame_first_partial_law_iff_pullback | (intros; apply GlobalTheory.frame_first_partial_law_iff_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapId
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCmp

theorem isMonHom_of_mul_points {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have e := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at e
    have e2 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have := e.symm
      exact mul_eq_left.1 this
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _)] using e2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem exists_iso_of_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  intro E _ _ _ H V _ t t' n
  have hp := n.cart.1
  have hw : n.cm.F ≫ t'.G.hom = t.G.hom := by simpa using hp.w
  haveI : IsIso n.cm.F := hp.isIso_fst_of_isIso
  let ψ : t.G ≅ t'.G := Over.isoMk (asIso n.cm.F) hw
  have hψ : ψ.hom.left = n.cm.F := rfl
  refine ⟨ψ, rfl, ?_, fun a => ?_, ?_, ?_⟩
  · refine isMonHom_of_mul_points _ fun T x y => ?_
    apply Over.OverMorphism.ext
    have e := n.cart.2 T x y (pushPt hp.w x) (pushPt hp.w y) rfl rfl
    rw [Over.comp_left, hψ, ← e]
    exact mul_left_congr (Category.comp_id _) _ _ (x ≫ ψ.hom) (y ≫ ψ.hom) rfl rfl
  · apply Over.OverMorphism.ext
    exact n.act a
  · refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, hψ]
  · obtain ⟨w, h1, -, h3⟩ := n.lin
    exact ⟨w, h1, h3⟩

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  first | exact @GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | exact GlobalTheory.ChartCmp.exists_iso_of_sabMap_id | (intros; apply GlobalTheory.ChartCmp.exists_iso_of_sabMap_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nabValN_congr_FK {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    (B : FB R d O) (B' : FB R' d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [Algebra R' k]
    (hF : B'.FK k = B.FK k) (hA : ∀ a, B'.actK k a = B.actK k a)
    (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {κ : Type} [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    nabValN B k h w0 m f cp u P = nabValN B' k h w0 m f cp u P := by
  unfold nabValN FB.hL
  rw [hF, hA]

theorem isIntPS_iff_exists_map (T : CDVR) {n d : ℕ} (f : PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro hf
    choose g hg using hf
    refine ⟨g, ?_⟩
    ext m
    exact (MvPowerSeries.coeff_map _ _ _).trans (hg m)
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem nuLocC_eq_nuAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  intro E _ _ _ H Dw l Xo c _ T io y C
  letI := io.toAlgebra
  intro BT hF hA e k a n
  unfold nuLocC nuAlg
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    refine iInf_le_of_le (MvPowerSeries.map (algebraMap T.V T.Fr) g) ?_
    refine iInf_le_of_le ((isIntPS_iff_exists_map T _).2 ⟨g, rfl⟩) ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _))
  · refine le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨g, rfl⟩ := (isIntPS_iff_exists_map T _).1 hf
    refine iInf_le_of_le g ?_
    exact le_of_eq (congrArg (nval T.V e) (nabValN_congr_FK C.ch.B BT T.Fr hF hA _ _ _ _ _ _ _)).symm

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepthStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChartDepth_eq_integralBiextDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  first | exact @GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | exact GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | (intros; apply GlobalTheory.ChartCmp.nuLocC_eq_nuAlg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.CarryCalc

variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem carries_iff (w : LB.Iso L' (L.pull F)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) :
    Carries L F w φ ε g g' ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
        gm r z (LB.wchart L (fun k => φ k ≫ F) p) (g'.s p) = pw w φ ε r z p q * gm r z (LB.wchart L' φ q) (g.s q) := by
  refine (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g')
    (fun j x hx => wchart_pull_le L F φ j hx) (fun j => rfl)).trans ⟨fun H Z r z p q hp hq => ?_, fun H Z r z p q hp hq => ?_⟩
  · have := H Z r z p q (Set.mem_iInter.1 hp) (Set.mem_iInter.1 hq)
    rw [Category.comp_id] at this
    exact this
  · rw [Category.comp_id]
    exact H Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

def fac (w : LB.Iso L' (L.pull F)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_carries {w : LB.Iso L' (L.pull F)} {φ : K → (Y ⟶ X')} {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)}
    {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (H : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, fac w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine ((carries_iff w φ ε g g').1 H Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [pw, fac, Category.assoc]

theorem carries_of_val {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
  have hc := (carries_iff w φ ε g t).2 hv
  have e : ∀ j, g'.s j = t.s j := fun j => unit_ext fun y hy => by
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
    have v' : val g' (𝟙 Y) y J = val t (𝟙 Y) y J := (h y J J' hJ hJ').trans (val_of_carries hc (𝟙 Y) hJ hJ').symm
    exact (gen_trans hg' (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).trans ((congrArg _ v').trans
      (gen_trans ht (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).symm)
  obtain ⟨s⟩ := g'
  obtain ⟨s'⟩ := t
  obtain rfl : s = s' := funext e
  exact hc

theorem exists_good' {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hM (ψ z)
  exact ⟨J, hJ⟩

end GlobalTheory.ChartCmp.CarryCalc

namespace GlobalTheory.ChartCmp
open CarryCalc

theorem carries_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  intro X X' L' L F _ w hL' hL hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y K _ φ ε g hg
    obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
    exact ⟨t, ht, (carries_iff w φ ε g t).2 hv⟩
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' hs _ _ _ _ Hg Hh
    have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
        (val g (𝟙 Y) y J' = val h (𝟙 Y) y J' ↔ val g' (𝟙 Y) y J = val h' (𝟙 Y) y J) := fun y J J' hJ hJ' => by
      rw [val_of_carries Hg (𝟙 Y) hJ hJ', val_of_carries Hh (𝟙 Y) hJ hJ',
        DVR.prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => fac w y J J' (𝟙 Y ≫ ψ)), mul_right_inj]
    refine ⟨fun C => corr_of_val hL fun y J hJ => ?_, fun C => corr_of_val hL' fun y J' hJ' => ?_⟩
    · obtain ⟨J', hJ'⟩ := exists_good' hL' y
      exact (key y J J' hJ hJ').1 (val_corr hJ' C _)
    · obtain ⟨J, hJ⟩ := exists_good' hL y
      exact (key y J J' hJ hJ').2 (val_corr hJ C _)
  · intro Y Z K _ φ ε g g' r g'' hg _ hg'' H C
    refine carries_of_val hL' hL hw (DVR.pullGen_isGen _ _ _ _ hg r) hg'' fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_pull hJ, val_pull hJ', val_of_carries H _ hJ hJ']
    simp only [Category.assoc]
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' p hg hh _ _ hp Hg Hh C
    refine carries_of_val hL' hL hw (DVR.mulGen_isGen _ _ _ _ _ _ _ hg hh) hp fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_mul hJ, val_mul hJ', val_of_carries Hg _ hJ hJ', val_of_carries Hh _ hJ hJ',
      Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
    rfl
  · intro Y K _ φ ε g g' H
    refine (carries_iff w φ _ _ _).2 fun Z r z p q hp hq => ?_
    refine (map_inv _ _).trans ((congrArg (·⁻¹) ((carries_iff w φ ε g g').1 H Z r z p q hp hq)).trans ?_)
    refine (mul_inv _ _).trans (congrArg₂ (· * ·) ?_ (map_inv _ _).symm)
    simp only [pw, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.ChartCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLinCombGenerator_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  first | exact @GlobalTheory.ChartCmp.carries_calculus | exact GlobalTheory.ChartCmp.carries_calculus | (intros; apply GlobalTheory.ChartCmp.carries_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRel
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRel
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V] {d : ℕ}

theorem ev_one_eq {n : ℕ} (a : Pt V n d) (f : PS V 1 d) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin d => a p.2) f := by
  unfold ev
  congr 1
  funext p
  rw [Matrix.cons_val_fin_one]

theorem cc_ev {k n : ℕ} (a : Fin k → Pt V n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS V k d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem cc_comp1 {n : ℕ} {φ : Pt V 1 d} {a : Pt V n d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) : MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by rw [Matrix.cons_val_fin_one]; exact ha i) _ (hφ i)

theorem germCompOne_assoc_of_constantCoeff_zero {n : ℕ} (ψ φ : Pt V 1 d) (a : Pt V n d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : comp1 (comp1 ψ φ) a = comp1 ψ (comp1 φ a) := by
  funext i
  simp only [comp1, ev_one_eq]
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => hφ p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem germCompOne_identityPoint_left {n : ℕ} (a : Pt V n d) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    comp1 (pt V (n := 1) d 0) a = a := by
  funext i
  simp only [comp1, ev_one_eq, pt]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem eq_comp1_inv {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by
  rw [← e, ← germCompOne_assoc_of_constantCoeff_zero φi φ a h.1 ha, h.2.2.2, germCompOne_identityPoint_left a ha]

def sub (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m k :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin k × Fin d => a p.1 p.2)

def sub1 (m : ℕ) {n : ℕ} (a : Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m 1 :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d => a p.2)

theorem hom_comp (m : ℕ) {κ κ' κ'' : Type} [Fintype κ'] [DecidableEq κ'] [Fintype κ''] [DecidableEq κ'']
    (g : κ → MvPowerSeries κ' V) (h : κ' → MvPowerSeries κ'' V) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) h) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) g) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun i => MvPowerSeries.subst h (g i)) := by
  rw [GermD.homAt_comp]
  congr 1
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m g hg, ExpChartJet.jetSubstPS_psJet m h hh,
    ExpChartJet.jetSubstPS_mk m _ (fun i => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hh) hh (hg i))]

theorem jetSchemeMap_pointFamily_comp_singlePoint (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) (b : Pt V k d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    sub m a ≫ sub1 m b = sub1 m (fun i => ev a (b i)) :=
  hom_comp m _ _ (fun p => hb p.2) (fun p => ha p.1 p.2)

theorem jetSchemeMap_singlePoint_comp_singlePoint (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by
  have e : sub1 m (comp1 φ a) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d =>
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => a q.2) (φ p.2)) := by
    simp only [sub1, comp1, ev_one_eq]
  rw [e]
  exact hom_comp m _ _ (fun p => hφ p.2) (fun p => ha p.2)

theorem eq_of_jetSchemeMap_singlePoint_universal {G : Over (Sp V)} [GrpObj G] {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {n : ℕ} {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (h : ∀ m, sub1 m a ≫ x m = sub1 m b ≫ x m) : a = b := by
  funext i
  refine GermFun.psJet_inj fun m => ?_
  have hk : RingHom.ker (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ^ (m + 1) = ⊥ := by
    have ea : (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) = Chart.jetAug V _ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow _ m
  have aa := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2)
  have ab := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)
  have h1 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ≫ (sub1 m a ≫ x m) = 1 := by
    rw [sub1, ← Category.assoc, GermD.homAt_comp, aa]
    exact hx.2.1 m
  have e := (hx.2.2 _ jetAug m hk _ h1).unique ⟨aa, rfl⟩ ⟨ab, h m⟩
  have e' := AlgHom.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2),
    ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)] at e'

theorem jptG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (m : ℕ) {n : ℕ} (i : Fin n) :
    jptG t (𝟙 (Sp V)) d x m i = sub1 m (pt V d i) ≫ x m := by
  have e : jetCopy (S := V) d m i = jetSubstPS (m := m) (fun p : Fin 1 × Fin d => pt V d i p.2) := by
    apply GermD.jet_hom_ext
    intro p
    rw [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => pt V d i p.2) (fun _ => MvPowerSeries.constantCoeff_X _),
      jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X, pt, ← MvPolynomial.coe_X]
    rw [psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rw [jptG, e]
  rfl

end GlobalTheory.ChartCmp.CoordLaw


open GlobalTheory.ChartCmp.CoordLaw in
theorem GlobalTheory.ChartCmp.law_act_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ φi hc hc' hu hinv hrel
  have hφ := hinv.1
  have hr : ∀ m, x' m = sub1 m φ ≫ x m := hrel
  have hpt : ∀ (j : Fin 2) i, MvPowerSeries.constantCoeff (pt V d j i) = 0 := fun j i => MvPowerSeries.constantCoeff_X _
  refine ⟨?_, fun a => ?_⟩
  · let A : Fin 2 → Pt V 2 d := ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)]
    have hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0 := by
      intro j i
      fin_cases j <;> exact cc_comp1 hφ (hpt _) i
    have hX : ∀ j, (fun i => ev A (pt V d j i)) = A j := fun j => funext fun i =>
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 2 × Fin d => hA p.1 p.2) (j, i)
    have key : comp1 φ B'.G.F = addOf B.G.F (comp1 φ (pt V (n := 2) d 0)) (comp1 φ (pt V (n := 2) d 1)) := by
      refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ B'.G.const) (fun i => cc_ev A hA _ (B.G.const i)) fun m => ?_
      have l : sub1 m B.G.F ≫ x m = _ := hc.law m
      have l' : sub1 m B'.G.F ≫ x' m = _ := hc'.law m
      have l2 := congrArg (fun f => sub m A ≫ f) l
      simp only [jptG_eq, MonObj.comp_mul, ← Category.assoc, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA B.G.const, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA (hpt _),
        hX] at l2
      simp only [jptG_eq, hr m, ← Category.assoc, jetSchemeMap_singlePoint_comp_singlePoint m _ φ B'.G.const hφ, jetSchemeMap_singlePoint_comp_singlePoint m _ φ (hpt _) hφ] at l'
      exact l'.trans l2.symm
    exact fun i => congrFun (eq_comp1_inv hinv B'.G.const key) i
  · refine eq_comp1_inv hinv (B'.A.const a) ?_
    refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ (B'.A.const a)) (cc_comp1 (B.A.const a) hφ) fun m => ?_
    have l : x m ≫ t.act.act a = sub1 m (B.A.act a) ≫ x m := hc.act m a
    have l' : x' m ≫ t.act.act a = sub1 m (B'.A.act a) ≫ x' m := hc'.act m a
    rw [← jetSchemeMap_singlePoint_comp_singlePoint m _ φ (B'.A.const a) hφ, ← jetSchemeMap_singlePoint_comp_singlePoint m φ _ hφ (B.A.const a), Category.assoc, Category.assoc, ← hr m,
      ← l', ← l, hr m, Category.assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_law_action_eq_transported_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  first | exact @GlobalTheory.ChartCmp.law_act_of_coordRel | exact GlobalTheory.ChartCmp.law_act_of_coordRel | (intros; apply GlobalTheory.ChartCmp.law_act_of_coordRel <;> assumption)
end
end

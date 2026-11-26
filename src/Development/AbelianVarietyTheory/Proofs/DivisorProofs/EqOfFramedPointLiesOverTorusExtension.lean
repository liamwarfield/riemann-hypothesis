module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Tors.OneOver

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ z J, Good D.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k := by
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' D.P.isLB z₀
  obtain ⟨wk, hwk, hv⟩ := GlobalTheory.TorusExt.exists_gen_val D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε k) hJ₀
    (val w (𝟙 _) z₀ J₀ ^ k)
  refine ⟨wk, hwk, fun z J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z₀ z
  have a₁ := CoefBasic.val_tr hwk (𝟙 _) hJ hJ₀
  have a₂ := CoefBasic.val_tr hw (𝟙 _) hJ hJ₀
  simp only [Category.id_comp] at a₁ a₂
  rw [CoefBasic.prod_line k b (CoefBasic.trU D.P.L z₀ J J₀)] at a₁
  rw [CoefBasic.prod_line 1 b (CoefBasic.trU D.P.L z₀ J J₀)] at a₂
  refine a₁.trans ?_
  rw [hv, a₂]
  simp only [pow_one, mul_pow, inv_pow]

theorem sumF_scale {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x : Ix → F} {v v' c : F} (h : SumF I F x v)
    (h' : SumF I F (fun i => c * x i) v') : v' = c * v := by
  have hl := (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix x x v v).2.1 h h (c - 1)
  have e : (fun i => (c - 1) * x i + x i) = fun i => c * x i := funext fun i => by ring
  rw [e, show (c - 1) * v + v = c * v by ring] at hl
  exact (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix (fun i => c * x i) x v' (c * v)).1 h' hl

theorem eq_of_liesOver : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ hw₀ g w w' x x' fr fr' hw hw' hfr hfr' H H'
  obtain ⟨wk, hwk, hvk⟩ := exists_frm_pow w hw 4
  obtain ⟨wk', hwk', hvk'⟩ := exists_frm_pow w' hw' 4
  obtain ⟨c, hc, -, hcoef⟩ := ((CoefBasic.coef_basic R D.toPre F 4 g).2.2 wk hwk).2.2.1 wk' hwk'
  have key : ∀ (t : SecA A F 4) (v v' : F), ValAt t x fr v → ValAt t x' fr' v' → v' = c * v := by
    intro t v v' hv hv'
    obtain ⟨s, hs⟩ : ∃ s, U.toUnifPre.ExpandsF F 4 w₀ t s := by
      obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 4) (by norm_num) w₀ hw₀
      exact ⟨e t, (he t _).2 rfl⟩
    have h1 := H 4 (by norm_num) wk hvk hwk t s v hs hv
    have h2 := H' 4 (by norm_num) wk' hvk' hwk' t s v' hs hv'
    rw [show coef s g wk' = fun χ => c * coef s g wk χ from funext (hcoef s)] at h2
    exact sumF_scale hI h1 h2
  obtain ⟨M, s, hcov, haff⟩ := (hL.1.ample _ A 4 le_rfl).2 ⊤ (isAffineOpen_top _)
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : SecA A F 4, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA v r z J =
        sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (TFK (R := R) F) A.A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec A.isLB (φ := fun _ : Fin 4 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => ((4 : ℕ) : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  choose a ha using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x hfr
  choose a' ha' using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x' hfr'
  have hrel : ∀ j, a' j = c * a j := fun j => key (v j) (a j) (a' j) (ha j) (ha' j)
  have hf : (x.left ≫ i') ≫ (A.A.hom ∣_ ⊤) = (x'.left ≫ i') ≫ (A.A.hom ∣_ ⊤) := by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
  have e : ∀ y : TFK (R := R) F ⟶ A.A,
      (ptSecT A.A y).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i' = y.left ≫ i' := fun y => by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
  have key2 : x.left ≫ i' = x'.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s
      (A.A.hom ∣_ ⊤) _ _ hf hcov (fun i => (haff i).1) r hr hsurj fun z => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
    obtain ⟨κ, hκ⟩ : ∃ κ : F →+* (TFK (R := R) F).left.presheaf.stalk z, ∀ b, cst (R := R) F z b = κ b :=
      ⟨CoefBasic.cstH (R := R) z, CoefBasic.cst_eq z⟩
    refine ⟨J, hJ, Units.map κ.toMonoidHom (Units.mk0 c hc) *
      val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J * (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)⁻¹, fun j => ?_⟩
    have p := (hv j _ (ptSecT A.A x).left z J hJ).symm.trans (ha j z J hJ)
    have q := (hv j _ (ptSecT A.A x').left z J hJ).symm.trans (ha' j z J hJ)
    rw [e] at p q
    rw [p, q, hrel j]
    have hinv := Units.inv_mul (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      hκ, map_mul, id] at hinv ⊢
    linear_combination (-(κ c * (val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J).val * κ (a j))) * hinv
  have := congrArg (fun q => q ≫ (A.A.hom ⁻¹ᵁ ⊤).ι) key2
  simp only [Category.assoc, hi, Category.comp_id] at this
  exact Over.OverMorphism.ext this

end GlobalTheory.Poinc.Tors.OneOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtensionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  first | exact @GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | exact GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExt

open NumberField IsDedekindDomain GlobalTheory.ChowHt GlobalTheory.Adelic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def locDeg (K : Type) [Field K] [NumberField K] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)

theorem mk_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    FinitePlace.mk w (algebraMap K L x) = FinitePlace.mk (w.under (𝓞 K)) x ^ locDeg K w := by
  set v := w.under (𝓞 K) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, locDeg, zero_pow (Nat.mul_pos he hf).ne']
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  have h0 : v.valuation K x ≠ 0 := (v.valuation K).ne_zero_iff.2 hx
  rw [FinitePlace.mk_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    ← HeightOneSpectrum.valuation_liesOver L v w x, map_pow, WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZeroMulInt.toNNReal_neg_apply _ h0, hn, locDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem finite_fiber (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have h : (v.asIdeal.primesOver (𝓞 L)).Finite := Set.toFinite _
  refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩

theorem sum_locDeg (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w ∈ (finite_fiber (L := L) v).toFinset, locDeg K w = Module.finrank K L := by
  classical
  have hsumN : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← hsumN]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (((finite_fiber (L := L) v).mem_toFinset).1 hw)).symm⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) fun _ _ => rfl
  refine ⟨⟨q.1, q.2.1, fun h0 => v.ne_bot ?_⟩, (Set.Finite.mem_toFinset _).2 (HeightOneSpectrum.ext q.2.2.over.symm),
    rfl⟩
  have h1 : v.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 L)) := q.2.2.over
  rw [h1, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem finsum_locDeg_mul (g : HeightOneSpectrum (𝓞 K) → ℝ) (hg : (Function.support g).Finite) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L), (locDeg K w : ℝ) * g (w.under (𝓞 K)) = Module.finrank K L * ∑ᶠ v, g v := by
  classical
  have hS : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ Function.support g}.Finite :=
    (hg.biUnion fun v _ => finite_fiber (L := L) v).subset fun w hw => Set.mem_biUnion hw rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun w hw => by
      simpa using right_ne_zero_of_mul hw,
    finsum_eq_sum g hg, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := hg.toFinset) (g := fun w => w.under (𝓞 K)) fun w hw => by simpa using hw]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← sum_locDeg v, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun w hw => by rw [(Set.Finite.mem_toFinset _).1 hw]
  ext w
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = Module.finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
    nsmul_eq_mul]

end Places

theorem iSup_pow {ι : Type} [Finite ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    ⨆ i, a i ^ m = (⨆ i, a i) ^ m := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm (ciSup_le fun j => pow_le_pow_left₀ (ha j) (le_ciSup (Set.finite_range _).bddAbove j) m) ?_
  rw [← hi]
  exact le_ciSup (f := fun i => a i ^ m) (Set.finite_range _).bddAbove i

theorem finite_support_log_iSup {K ι : Type} [Field K] [NumberField K] [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (⨆ k, v (z k))).Finite := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  refine (Set.finite_iUnion fun k : {k // z k ≠ 0} => FinitePlace.hasFiniteMulSupport k.2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  refine hv ?_
  have : ⨆ k, v (z k) = 1 := le_antisymm (ciSup_le fun k => by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_le_one
      · exact (h ⟨k, h0⟩).le)
    ((h ⟨k₀, hk₀⟩).ge.trans (le_ciSup (f := fun k => v (z k)) (Set.finite_range _).bddAbove k₀))
  simp only [this, Real.log_one]

theorem finsum_log_iSup_algebraMap {K L ι : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ k, w (algebraMap K L (z k))) =
      Module.finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (z k)) := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm,
    ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    ← finsum_locDeg_mul _ ((finite_support_log_iSup hz).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn)]
  refine finsum_congr fun w => ?_
  rw [← Real.log_pow, ← iSup_pow _ fun _ => apply_nonneg _ _]
  exact congrArg Real.log (iSup_congr fun k => mk_algebraMap w (z k))

theorem pointHeight_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw _ K' _ _ _ _ _ y hy
  classical
  have hz : (fun k => ∑ j, algebraMap F K (w j k) * y j) ≠ 0 := fun h => by
    have hp := finSize_pos hw (algebraMap F K) AbsoluteValue.trivial hy
    have h' : ∀ k, ∑ j, algebraMap F K (w j k) * y j = 0 := congrFun h
    simp [finSize, h'] at hp
  have h₁ := finsum_log_iSup_algebraMap (L := K') hz
  have h₂ := sum_comp_algebraMap (L := K')
    fun τ : K →+* ℂ => Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, RingHom.comp_apply] at h₂
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  rw [pointHeight_eq, pointHeight_eq, h₂, ← Module.finrank_mul_finrank ℚ K K']
  simp only [finSize, ← FinitePlace.coe_apply]
  rw [h₁]
  push_cast
  field_simp

end GlobalTheory.Adelic.HeightExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMapStatement
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K), y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | exact GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | (intros; apply GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace AlgChart

variable (c c' : AlgChart p σ D) {S : Set (CxPts p σ)} {y : CxPts p σ} {f g : CxPts p σ → ℝ}

def levi (f : CxPts p σ → ℝ) (y : CxPts p σ) (ξ : Fin D → ℂ) : ℝ :=
  (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

def dtrans (y : CxPts p σ) (ξ : Fin D → ℂ) : Fin D → ℂ :=
  fun b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (WithLp.toLp 2 ξ) b

variable {c c'}

theorem levi_congr (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S) (h : ∀ z ∈ S, f z = g z)
    (ξ : Fin D → ℂ) : c.levi f y ξ = c.levi g y ξ :=
  congrArg Complex.re (leviV_congr (eventually_of_mem
    ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      congrArg Complex.ofReal (h _ hv.2)) ξ)

theorem levi_add (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y))
    (hg : ContDiffAt ℝ 2 (g ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => f z + g z) y ξ = c.levi f y ξ + c.levi g y ξ :=
  (congrArg Complex.re (flA_leviV_add hf hg ξ)).trans (Complex.add_re _ _)

theorem levi_const_mul (a : ℝ) (hf : ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y)) (ξ : Fin D → ℂ) :
    c.levi (fun z => a * f z) y ξ = a * c.levi f y ξ :=
  (congrArg Complex.re (LocalMaximumSecondDerivative.leviV_ofReal_const_mul a hf ξ)).trans (Complex.re_ofReal_mul _ _)

theorem levi_log_normSq {u : CxPts p σ → ℂ} (hS : IsOpen S) (hy : y ∈ c.e.source) (hyS : y ∈ S)
    (hu : DifferentiableOn ℂ (u ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' S)) (h0 : u y ≠ 0)
    (ξ : Fin D → ℂ) : c.levi (fun z => Real.log (‖u z‖ ^ 2)) y ξ = 0 :=
  congrArg Complex.re (flA_leviV_log_normSq (h := u ∘ c.e.symm)
    (eventually_of_mem ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS)) fun _ hv =>
      hu.differentiableAt ((isOpen_over c.e hS).mem_nhds hv))
    (by rwa [Function.comp_apply, c.e.left_inv hy]) ξ)

theorem levi_trans (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source)
    (hf : ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y)) (ξ : Fin D → ℂ) :
    c.levi f y ξ = c'.levi f y (c.dtrans c' y ξ) := by
  have ho := isOpen_over c.e c'.e.open_source
  have hn := ho.mem_nhds (mem_over c.e hy hy')
  have ht : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
    (((contDiffOn_piLp 2).2 fun a => contDiffOn_of_differentiableOn D _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hU : ContDiffAt ℝ 2 (fun v => (f (c'.e.symm v) : ℂ)) ((c'.e ∘ c.e.symm) (c.e y)) :=
    e ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have := flA_leviV_comp hU ht ξ
  rw [e] at this
  refine congrArg Complex.re (Eq.trans (leviV_congr (eventually_of_mem hn fun v hv => ?_) ξ) this)
  simp only [Function.comp_apply, c'.e.left_inv hv.2]

theorem dtrans_ne_zero (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) {ξ : Fin D → ℂ}
    (hξ : ξ ≠ 0) : c.dtrans c' y ξ ≠ 0 := fun h => by
  have hd : transDet c.e c'.e y ≠ 0 := rv_chart c c' hy hy' ▸
    rv_ne_zero _ _ (c.source_subset hy) (c'.source_subset hy')
  have hi := (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  have := LinearMap.ker_eq_bot'.1 hi (WithLp.toLp 2 ξ) (PiLp.ext fun b => congrFun h b)
  exact hξ (congrArg WithLp.ofLp this)

end AlgChart

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)} {y : CxPts p σ}

theorem SmoothOn.contDiffAt_two {f : CxPts p σ → ℝ} (h : R.SmoothOn S f) (hS : IsOpen S)
    {c : AlgChart p σ D} (hy : y ∈ c.e.source) (hyS : y ∈ S) :
    ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) :=
  ((h.chart hS c).contDiffAt ((isOpen_over c.e hS).mem_nhds (mem_over c.e hy hyS))).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem levi_eq_of_add_log {f g : CxPts p σ → ℝ} {u : CxPts p σ → ℂ} (hS : IsOpen S)
    (hf : R.SmoothOn S f) (hu : R.HoloOn S u) (h0 : ∀ z ∈ S, u z ≠ 0)
    (h : ∀ z ∈ S, g z = f z + Real.log (‖u z‖ ^ 2)) {c : AlgChart p σ D} (hy : y ∈ c.e.source)
    (hyS : y ∈ S) (ξ : Fin D → ℂ) : c.levi g y ξ = c.levi f y ξ := by
  rw [AlgChart.levi_congr hS hy hyS h, AlgChart.levi_add (hf.contDiffAt_two hS hy hyS)
    ((hu.smoothOn_log hS h0).contDiffAt_two hS hy hyS),
    AlgChart.levi_log_normSq hS hy hyS (hu.chart hS c) (h0 y hyS), add_zero]

end AnRead

namespace Weight

open AnRead

variable {R R' : AnRead p σ D} {A B : LB Y} {φ : Weight p σ B} {ψ : Weight p σ A}
  {c : AlgChart p σ D} {y : CxPts p σ}

theorem IsSmooth.contDiffAt_two (h : φ.IsSmooth R) {i : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : ContDiffAt ℝ 2 (φ.φ i ∘ c.e.symm) (c.e y) :=
  (h i).contDiffAt_two (isOpen_ptsIn _) hy hi

theorem IsSmooth.levi_frame (h : φ.IsSmooth R) {i j : B.ι} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) (ξ : Fin D → ℂ) :
    c.levi (φ.φ i) y ξ = c.levi (φ.φ j) y ξ :=
  levi_eq_of_add_log ((isOpen_ptsIn (B.U i)).inter (isOpen_ptsIn (B.U j)))
    ((h j).mono inter_subset_right) (u := gv p σ B i j)
    (holoOn_ev_of_subset _ fun _ => mem_ptsIn_inf.2) (fun _ hz => gv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [φ.trans i j z hz.1 hz.2, sub_add_cancel]) hy ⟨hi, hj⟩ ξ

theorem IsSmooth.strictPos_of_exists (hs : φ.IsSmooth R)
    (h : ∀ y, ∃ (c : AlgChart p σ D) (i : B.ι), y ∈ c.e.source ∧ y ∈ ptsIn p σ (B.U i) ∧
      ∀ ξ, ξ ≠ 0 → 0 < c.levi (φ.φ i) y ξ) : φ.StrictPos R := fun j c' y hy ξ hξ => by
  obtain ⟨c, i, hc, hi, h⟩ := h y
  exact (h _ (AlgChart.dtrans_ne_zero hy.1 hc hξ)).trans_eq ((hs.levi_frame hc hi hy.2 _).trans
    (AlgChart.levi_trans hy.1 hc (hs.contDiffAt_two hc hy.2) ξ).symm)

theorem levi_tens (hψ : ψ.IsSmooth R) (hφ : φ.IsSmooth R) {i : (CechPic.tens A B).ι}
    (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ ((CechPic.tens A B).U i)) (ξ : Fin D → ℂ) :
    c.levi ((ψ.tens φ).φ i) y ξ = c.levi (ψ.φ i.1) y ξ + c.levi (φ.φ i.2) y ξ :=
  AlgChart.levi_add (hψ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).1)
    (hφ.contDiffAt_two hy (mem_ptsIn_inf.1 hi).2) ξ

theorem levi_zpow (hφ : φ.IsSmooth R) (n : ℤ) {j : PUnit → B.ι} (hy : y ∈ c.e.source)
    (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) (ξ : Fin D → ℂ) :
    c.levi ((φ.zpow n).φ j) y ξ = n * c.levi (φ.φ (j PUnit.unit)) y ξ := by
  rw [funext (φ.zpow_φ n j)]
  exact AlgChart.levi_const_mul _ (hφ.contDiffAt_two hy hj) ξ

theorem SemiPos.tens (h' : ψ.SemiPos R) (h : φ.SemiPos R) (hψ : ψ.IsSmooth R)
    (hφ : φ.IsSmooth R) : (ψ.tens φ).SemiPos R := fun i c y hy ξ =>
  (add_nonneg (h' _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).1⟩ ξ)
    (h _ c y ⟨hy.1, (mem_ptsIn_inf.1 hy.2).2⟩ ξ)).trans_eq (levi_tens hψ hφ hy.1 hy.2 ξ).symm

theorem SemiPos.zpow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) {n : ℤ} (hn : 0 ≤ n) :
    (φ.zpow n).SemiPos R := fun j c y hy ξ =>
  (mul_nonneg (Int.cast_nonneg hn) (h _ c y ⟨hy.1, mem_pow_iff.1 hy.2⟩ ξ)).trans_eq
    (levi_zpow hφ n hy.1 (mem_pow_iff.1 hy.2) ξ).symm

theorem SemiPos.pow (h : φ.SemiPos R) (hφ : φ.IsSmooth R) (n : ℕ) : (φ.pow n).SemiPos R :=
  h.zpow hφ (Int.natCast_nonneg n)

theorem semiPos_fs {α : Type*} [Fintype α] {e : α → B.ι → CxPts p σ → ℂ} (hB : B.IsLB)
    (he : ∀ a, e a ∈ R.holSec B) (h : NoCommonZero e) :
    (fs hB e (fun a => (he a).1) h).SemiPos R := fun i c y hy ξ => by
  have ho := isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hc (a) : ContDiffAt ℂ 2 (e a i ∘ (R.chart c).e.symm) ((R.chart c).e y) :=
    ((contDiffOn_of_differentiableOn D _ _ ho ((he a).2 i c)).contDiffAt
      (ho.mem_nhds (mem_over _ hy.1 hy.2))).of_le (WithTop.coe_le_coe.2 le_top)
  have hs (v) : ∑ j, Complex.normSq ((e ((Fintype.equivFin α).symm j) i ∘ (R.chart c).e.symm) v) =
      ∑ a, ‖e a i ((R.chart c).e.symm v)‖ ^ 2 :=
    Fintype.sum_equiv (Fintype.equivFin α).symm _ _ fun _ => Complex.normSq_eq_norm_sq _
  have := leviV_log_sum_nonneg (fun j => contDiffAt_normSq_comp (hc ((Fintype.equivFin α).symm j)))
    (fun j => logPshAt_normSq (hc _))
    (by rw [hs, (R.chart c).e.left_inv hy.1]; exact h.sum_pos hy.2) ξ
  simp only [hs] at this
  exact this

end Weight

namespace WeightFamily.Reading

variable [SmoothOfRelativeDimension D p] {R : AnRead p σ D} {κ : Type} [Fintype κ] [DecidableEq κ]
  [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] {F : WeightFamily R κ} {B : LB Y}
  {m : Option κ → ℤ} {r : F.Reading B m} {φ : Weight p σ B}

end WeightFamily.Reading

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemConj
private theorem UpperTheory.Reformulated.B.Yt3.mem_conj {G : Type} [Group G] {K : Subgroup G} {g y : G} :
    y ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem UpperTheory.Reformulated.B.Yt3.exists_reps :
    ∀ {G : Type} [inst : Group G] {K : Subgroup G} {g : G},
      (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).relIndex K ≠ (0 : ℕ) →
        ∃ (R : Finset G),
          (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
            ∀ (x : G), (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ : G, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  intro G _ K g h
  classical
  set H : Subgroup K :=
    (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) g)) K).subgroupOf K with hH
  have hfin : Finite (K ⧸ H) := Nat.finite_of_card_ne_zero h
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have key : ∀ (a b : K) (k : G), k ∈ K →
      ((((a : G) * g)⁻¹ * ((b : G) * g * k) ∈ K) ↔ (a : K ⧸ H) = (b : K ⧸ H)) := by
    intro a b k hk
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, UpperTheory.Reformulated.B.Yt3.mem_conj,
      ← mul_assoc, K.mul_mem_cancel_right hk]
    simp [mul_assoc]
  refine ⟨Finset.univ.image (fun q : K ⧸ H => ((q.out : K) : G) * g), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out).2, 1, K.one_mem, (mul_one _).symm⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    refine ⟨(((((⟨k₁, hk₁⟩ : K) : K ⧸ H)).out : K) : G) * g,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨k₁, hk₁⟩ k₂ hk₂).2 (QuotientGroup.out_eq' _)
    · rintro γ ⟨hγ, hx⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      have := (key _ ⟨k₁, hk₁⟩ k₂ hk₂).1 hx
      rw [QuotientGroup.out_eq'] at this
      rw [this]
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.HeckeLabels

section Abstract

theorem forall_exists_transfer {X X' Z Z' : Type} {L : X → Prop} {L' : X' → Prop} {I : Z → Prop} {I' : Z' → Prop}
    (p : X → X') (q : Z → Z') (p1 : ∀ y, L y → L' (p y)) (p2 : ∀ y', L' y' → ∃ y, L y ∧ p y = y')
    (q1 : ∀ z, I z → I' (q z)) (q2 : ∀ z', I' z' → ∃ z, I z ∧ q z = z') {P : X → Z → Prop} {P' : X' → Z' → Prop}
    (h : ∀ y z, P y z ↔ P' (p y) (q z)) :
    (∀ y, L y → ∃ z, I z ∧ P y z) ↔ ∀ y', L' y' → ∃ z', I' z' ∧ P' y' z' := by
  constructor
  · intro H y' hy'
    obtain ⟨y, hy, rfl⟩ := p2 y' hy'
    obtain ⟨z, hz, e⟩ := H y hy
    exact ⟨q z, q1 z hz, (h y z).1 e⟩
  · intro H y hy
    obtain ⟨z', hz', e⟩ := H _ (p1 y hy)
    obtain ⟨z, hz, rfl⟩ := q2 z' hz'
    exact ⟨z, hz, (h y z).2 e⟩

variable {R : Type} [CommRing R] {n : ℕ}

def StdDiv (O : Subring R) (ε : R) (t : Fin n → R) (m : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∀ i, (ε • B *ᵥ z) i ∈ O) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • y = ε • B *ᵥ z) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z)) ∧
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∃ y : Fin n → R, (∀ i, y i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z))

theorem conj_mem_UJ (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ σ J) :
    h⁻¹ * g * h ∈ Formalism.UG.UJ σ J' := by
  have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
  show Formalism.UG.cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'
  have e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹ * g * h).1) * J * (h.1 * (h⁻¹ * g * h).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ h.1 * (Formalism.UG.cT σ g.1 * J * g.1) * h.1 := by
        rw [e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg', hh]

theorem inv_frame (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') : Formalism.UG.cT σ (h⁻¹).1 * J' * (h⁻¹).1 = J := by
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹).1) * J * (h.1 * (h⁻¹).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_reps {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hK : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    ∃ R : Finset G, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Yt3.exists_reps hK

theorem relIndex_conj_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J U L : Subgroup G}
    (hJ : IsCompact (J : Set G)) (hU : IsOpen (U : Set G)) (hL : ∀ k ∈ L, k ∈ U → k ∈ J) {g : G} (hg : g ∈ L) :
    ((J ⊓ L).map (MulAut.conj g).toMonoidHom).relIndex (J ⊓ L) ≠ 0 := by
  let U' : Subgroup G := U.comap (MulAut.conj g⁻¹).toMonoidHom
  have hU' : IsOpen (U' : Set G) := hU.preimage (show Continuous fun u : G => g⁻¹ * u * g⁻¹⁻¹ by fun_prop)
  have : CompactSpace J := isCompact_iff_compactSpace.1 hJ
  have h1 : U'.relIndex J ≠ 0 := by
    have : Finite (J ⧸ U'.subgroupOf J) :=
      Subgroup.quotient_finite_of_isOpen _ (hU'.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  have h2 : U'.relIndex (J ⊓ L) ≠ 0 := fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  rw [← Subgroup.inf_relIndex_right] at h2
  refine fun h => h2 (Subgroup.relIndex_eq_zero_of_le_left ?_ h)
  rintro k ⟨hk, hk'⟩
  have h3 : g⁻¹ * k * g⁻¹⁻¹ ∈ L := mul_mem (mul_mem (inv_mem hg) hk'.2) (inv_mem (inv_mem hg))
  exact ⟨g⁻¹ * k * g⁻¹⁻¹, ⟨hL _ h3 hk, h3⟩, by simp [mul_assoc]⟩

end Abstract

section Place

open GlobalTheory.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : CMData F E) (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}

theorem divG_iff {e : AF F ⊗[F] E} (he : ∀ w, w ≠ v → evF E w (finP F E e) = 0)
    {h : GL (Fin V.rank) (Fv F v ⊗[F] E)} (hh : IsFrameAt V v h) (ϖ : E) (d : Fin V.rank → ℤ)
    (g : HA (AF F) hc.sig V.gram) :
    DivG hc V e ϖ d g ↔ StdDiv (ordAt E v) (evF E v (finP F E e)) (fun i => inclR (Fv F v) (ϖ ^ d i))
      (h⁻¹ * locMat hc V v g * h).1 := by
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1 *ᵥ ((h⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1 *ᵥ (h.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let q : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun z i => evF E v (z i)
  let p : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun y => (h⁻¹).1 *ᵥ q y
  have p1 : ∀ y, y ∈ lamHat F V → ∀ i, p y i ∈ ordAt E v := fun y hy => (hh _).1 ((mem_lamHat_iff V _).1 hy v)
  have p2 : ∀ y' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y' i ∈ ordAt E v) → ∃ y, y ∈ lamHat F V ∧ p y = y' :=
    fun y' hy' => ⟨_, GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hh (h.1 *ᵥ y')).2 (by rwa [hback'])), by
      simp only [p, q, evF_sgT_self]; exact hback' y'⟩
  have q1 : ∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∀ i, q z i ∈ ordAt E v :=
    fun z hz i => (IntLocal.mem_intA_iff F E _).1 (hz i) v
  have q2 : ∀ z' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, z' i ∈ ordAt E v) →
      ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧ q z = z' :=
    fun z' hz' => ⟨_, fun i => GlobalTheory.PlaceDiv.sgT_mem_intA v (hz' i), funext fun i => evF_sgT_self v _⟩
  have qv : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z, q (A *ᵥ z) = A.map (evF E v) *ᵥ q z :=
    fun A z => funext fun i => RingHom.map_mulVec (evF E v) A z i
  have qe : ∀ X, q (fun a => finP F E e * X a) = evF E v (finP F E e) • q X :=
    fun X => funext fun i => map_mul (evF E v) _ _
  have key : ∀ X Y : Fin V.rank → Af F ⊗[F] E, ((fun a => finP F E e * X a) = fun a => finP F E e * Y a) ↔
      evF E v (finP F E e) • p X = evF E v (finP F E e) • p Y := by
    intro X Y
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨fun H => by rw [H], fun H => funext fun a => evF_ext fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      have := congrArg (h.1 *ᵥ ·) H
      simp only [hback] at this
      exact congrFun this a
    · rw [map_mul, map_mul, he w hw, zero_mul, zero_mul]
  have pB : ∀ (B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z,
      p (B *ᵥ z) = ((h⁻¹).1 * B.map (evF E v)) *ᵥ q z := fun B z => by
    simp only [p, qv, Matrix.mulVec_mulVec]
  have pg : ∀ y, p (finMat hc.sig V.gram g *ᵥ y) = (h⁻¹ * locMat hc V v g * h).1 *ᵥ p y := fun y => by
    simp only [p, qv, Units.val_mul, ← Matrix.mulVec_mulVec, hback, locMat_val]
  have qt : ∀ z : Fin V.rank → Af F ⊗[F] E, q (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) =
      (fun i => inclR (Fv F v) (ϖ ^ d i)) * q z := fun z => funext fun i => by
    show evF E v _ = _ * evF E v _
    rw [map_mul, evF_finP_incl]
  have c1 : ∀ X : Fin V.rank → Af F ⊗[F] E, (fun a => finP F E e * X a) ∈ lamHat F V ↔
      ∀ i, (evF E v (finP F E e) • p X) i ∈ ordAt E v := by
    intro X
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨p1 _, fun H => (mem_lamHat_iff V _).2 fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      exact (hh _).2 H
    · simp only [map_mul, he w hw, zero_mul]
      exact zero_mem _
  have sB : ∀ B' : Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E),
      ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E), (h⁻¹).1 * B.map (evF E v) = B' := fun B' => by
    refine ⟨(h.1 * B').map (sgT E v), ?_⟩
    have : ((h.1 * B').map (sgT E v)).map (evF E v) = h.1 * B' := Matrix.ext fun i j => evF_sgT_self v _
    rw [this, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold DivG StdDiv
  rw [Function.Surjective.exists sB]
  refine exists_congr fun B => and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro H z' hz'
      obtain ⟨z, hz, rfl⟩ := q2 z' hz'
      rw [← pB, ← c1]
      exact H z hz
    · intro H z hz
      rw [c1, pB]
      exact H _ (q1 z hz)
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pB]
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pg, pB, qt]
  · exact forall_exists_transfer q p q1 q2 p1 p2 fun z y => by rw [key, pg, pB, qt]

end Place

section CM

open GlobalTheory.PlaceComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_div_iff (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {e f : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (hf : IsIdemOf E v f) (hef : e * f = e)
    (ϖ : E) (d : ℕ → ℤ) {n : ℕ} (hn : V.rank = n) :
    (∃ g, Supp hc V f g ∧ DivG hc V e ϖ (fun i => d i.1) g) ↔
      ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
        StdDiv (ordAt E v) (evF E v (finP _ E e)) (fun i => inclR (Fv _ v) (ϖ ^ d i.1)) u.1 := by
  subst hn
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  have he : ∀ w, w ≠ v → evF E w (finP _ E e) = 0 := fun w hw => by
    rw [← hef, map_mul, map_mul, hf.2.2 w hw, mul_zero]
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨_, conj_mem_UJ _ hon (locMat_mem hc V v g), (divG_iff hc V he hfr ϖ _ g).1 hg⟩
  · rintro ⟨u, hu, hd⟩
    obtain ⟨g, hg, e1⟩ := (GlobalTheory.SuppLocal.supp_local _ E hc V v f hf).2.2 _ (conj_mem_UJ _ (inv_frame _ hon) hu)
    refine ⟨g, hg, (divG_iff hc V he hfr ϖ _ g).2 ?_⟩
    have : h⁻¹ * locMat hc V v g * h = u := by rw [e1]; group
    rwa [this]

end CM

section Host

open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Host

end GlobalTheory.HeckeLabels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult in
open scoped ComplexOrder in
theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))
end GlobalTheory.FrameEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem nrmG_succ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) :
    nrmG θ (r + 1) δ = nrmG θ r δ * (⇑θ)^[r] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem iter_hom_mul {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x y : H) :
    (⇑θ)^[r] (x * y) = (⇑θ)^[r] x * (⇑θ)^[r] y := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_mul, ih]

theorem iter_hom_inv {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x : H) :
    (⇑θ)^[r] x⁻¹ = ((⇑θ)^[r] x)⁻¹ := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_inv, ih]

theorem nrmG_twConj {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H) :
    nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧
      δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  induction r with
  | zero => simp [nrmG]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [nrmG_succ, nrmG_succ, h1, iter_hom_mul, iter_hom_mul,
        iter_hom_inv, Function.iterate_succ_apply]
      group
    · rw [nrmG_succ, map_mul, ← mul_assoc, h2, mul_assoc, ← Function.iterate_succ_apply' (⇑θ), mul_assoc]

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConjStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormProductIterate_twistedConj : ∀ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H), nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧ δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  first | (exact @GlobalTheory.LKMid.nrmG_twConj) | (exact GlobalTheory.LKMid.nrmG_twConj) | (intros; apply GlobalTheory.LKMid.nrmG_twConj  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
end

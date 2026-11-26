module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HSAbs

theorem coeFn_finsum {X : Type} [MeasurableSpace X] {ν : Measure X} {κ : Type} (s : Finset κ)
    (f : κ → Lp ℂ 2 ν) : (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

theorem pointwise {X : Type} [MeasurableSpace X] {ν : Measure X}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∀ᵐ x ∂ν, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ≤ C ^ 2 := by
  classical

  let w : (s → ℂ) → H := fun c => ∑ j : s, c j • e j
  have hon : Orthonormal ℂ (fun j : s => e j) := he.comp _ Subtype.val_injective
  have hw2 : ∀ c, ‖w c‖ ^ 2 = ∑ j : s, ‖c j‖ ^ 2 := by
    intro c
    have h := hon.inner_sum c c Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (s → ℂ)
  have hD : ∀ c ∈ D, ∀ᵐ x ∂ν, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    intro c _
    have hlin : T (w c) = ∑ j : s, c j • T (e j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, map_sum, map_smul]
    have hsm : ∀ᵐ x ∂ν, ∀ j : s, (c j • T (e j) : Lp ℂ 2 ν) x = c j * T (e j) x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (T (e j))] with x hx
      rw [hx]; rfl
    filter_upwards [hT (w c), coeFn_finsum (ν := ν) Finset.univ (fun j : s => c j • T (e j)), hsm]
      with x hx hsum hj
    rw [hlin, hsum] at hx
    simpa only [hj] using hx
  filter_upwards [(ae_ball_iff hDc).2 hD] with x hx

  have hall : ∀ c : s → ℂ, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    have hcl : IsClosed {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure D ⊆ {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      hcl.closure_subset_iff.2 fun c hc => hx c hc
    intro c
    exact hsub (hDd.closure_eq ▸ Set.mem_univ c)

  set S := ∑ j : s, ‖T (e j) x‖ ^ 2 with hS
  have key := hall fun j => (starRingEnd ℂ) (T (e j) x)
  have hL : ‖∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x‖ = S := by
    have : ∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x = ((S : ℝ) : ℂ) := by
      rw [hS]; push_cast
      exact Finset.sum_congr rfl fun j _ => RCLike.conj_mul _
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR : ‖w (fun j => (starRingEnd ℂ) (T (e j) x))‖ ^ 2 = S := by
    rw [hw2]
    exact Finset.sum_congr rfl fun j _ => by rw [RCLike.norm_conj]
  rw [hL] at key
  have hnn := norm_nonneg (w fun j => (starRingEnd ℂ) (T (e j) x))
  have hfin : S ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - ‖w fun j => (starRingEnd ℂ) (T (e j) x)‖)]
  rw [← Finset.sum_coe_sort s (fun i => ‖T (e i) x‖ ^ 2)]
  exact hfin

theorem sum_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ C ^ 2 * ν.real univ := by
  have hn : ∀ f : Lp ℂ 2 ν, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    intro f
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hint : ∀ f : Lp ℂ 2 ν, Integrable (fun x => ‖f x‖ ^ 2) ν := by
    intro f
    have hm : MemLp f ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp f
    exact hm.integrable_norm_pow (by norm_num)
  calc ∑ i ∈ s, ‖T (e i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ∂ν := by
        rw [integral_finsetSum s fun i _ => hint (T (e i))]
        exact Finset.sum_congr rfl fun i _ => hn _
    _ ≤ ∫ _x, C ^ 2 ∂ν :=
        integral_mono_ae (integrable_finsetSum s fun i _ => hint (T (e i)))
          (integrable_const _) (pointwise e he T C hT s)
    _ = C ^ 2 * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

end GlobalTheory.HSAbs


open GlobalTheory.HSAbs in
theorem GlobalTheory.isHilbertSchmidt_of_ae_bounded : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  intro X _ ν _ H _ _ _ T C hT
  unfold GlobalTheory.OpTrace.IsHilbertSchmidt
  refine summable_of_sum_le (c := C ^ 2 * ν.real univ) (fun i => sq_nonneg _) fun u => ?_
  exact GlobalTheory.HSAbs.sum_le _ (GlobalTheory.OpTrace.stdBasis (H := H)).orthonormal T C hT u
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  first | exact @GlobalTheory.isHilbertSchmidt_of_ae_bounded | exact GlobalTheory.isHilbertSchmidt_of_ae_bounded | (intros; apply GlobalTheory.isHilbertSchmidt_of_ae_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem sabMap_exists_iso_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {j : S' ⟶ S} (m : SABMap s' s j) :
    ∃ e : s'.G ≅ (Over.pullback j).obj s.G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst s.G.hom j = m.φ ∧
      ∀ a, s'.act.act a ≫ e.hom = e.hom ≫ (Over.pullback j).map (s.act.act a) := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback s.G _)
  have hφ' : e.hom.left ≫ pullback.fst s.G.hom j = m.φ := hφ
  refine ⟨e, he, hφ', fun a => ?_⟩
  have A : ((Over.pullback j).map (s.act.act a)).left ≫ pullback.fst s.G.hom _ =
        pullback.fst s.G.hom _ ≫ (s.act.act a).left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, A]
    rw [reassoc_of% hφ', hφ', m.act a]
  · exact (Over.w _).trans (Over.w _).symm

theorem conj_comp_eq_id_pow {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (u : A ≅ B) (u' : A' ≅ B') [IsMonHom u.hom] (f : B ⟶ B') (f' : B' ⟶ B) (N : ℕ) (h : f ≫ f' = 𝟙 B ^ N) :
    (u.hom ≫ f ≫ u'.inv) ≫ (u'.hom ≫ f' ≫ u.inv) = 𝟙 A ^ N := by
  have : IsMonHom u.inv := inferInstance
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem pullback_map_id_pow {S S' : Scheme.{0}} (j : S' ⟶ S) (A : Over S) [GrpObj A] (N : ℕ) :
    (Over.pullback j).map (𝟙 A ^ N) = 𝟙 ((Over.pullback j).obj A) ^ N := by
  induction N with
  | zero => simpa using Functor.map_one (Over.pullback j)
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]; simp

theorem ext_of_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] (F : G.G ⟶ G'.G)
    (d : t.G ≅ Fib Xo x) (d' : t'.G ≅ Fib Xo x') [IsMonHom d.hom] [IsMonHom d'.hom]
    (e : t.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G.G)
    (e' : t'.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G'.G)
    (hd : d.hom.left ≫ pullback.fst _ _ = m₁.φ) (hd' : d'.hom.left ≫ pullback.fst _ _ = n₁.φ)
    (he : e.hom.left ≫ pullback.fst _ _ = m₂.φ) (he' : e'.hom.left ≫ pullback.fst _ _ = n₂.φ)
    (hF : (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) :
    Ext m₁ m₂ n₁ n₂ f F := by
  have A : ((Over.pullback (spMap (algebraMap T.V T.Fr))).map F).left ≫ pullback.fst G'.G.hom _ =
        pullback.fst G.G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have B : (d.hom ≫ f ≫ d'.inv) ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap T.V T.Fr))).map F := by
    rw [hF]; simp
  refine ⟨d.hom ≫ f ≫ d'.inv, inferInstance, ?_, fun g g' h1 h2 h3 h4 => ?_⟩
  · rw [← he', ← he, Category.assoc, ← A, ← Category.assoc, ← Category.assoc e.hom.left, ← Over.comp_left,
      ← Over.comp_left, B]
  · obtain rfl : g = d.hom.left := pullback.hom_ext (h1.trans hd.symm) (h2.trans (Over.w d.hom).symm)
    obtain rfl : g' = d'.hom.left := pullback.hom_ext (h3.trans hd'.symm) (h4.trans (Over.w d'.hom).symm)
    have C : d.hom ≫ f = (d.hom ≫ f ≫ d'.inv) ≫ d'.hom := by simp
    exact congrArg (fun k => k.left) C

theorem conj_comm {C : Type*} [Category C] {A B P A' B' P' : C} (e : A ≅ P) (d : A ≅ B) (e' : A' ≅ P') (d' : A' ≅ B')
    (f : B ⟶ B') (a : A ⟶ A) (b : B ⟶ B) (p : P ⟶ P) (a' : A' ⟶ A') (b' : B' ⟶ B') (p' : P' ⟶ P')
    (hd : a ≫ d.hom = d.hom ≫ b) (he : a ≫ e.hom = e.hom ≫ p) (hd' : a' ≫ d'.hom = d'.hom ≫ b')
    (he' : a' ≫ e'.hom = e'.hom ≫ p') (h : b ≫ f = f ≫ b') :
    p ≫ (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv = ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) ≫ p' := by
  have h1 : p ≫ e.inv = e.inv ≫ a := by rw [Iso.eq_inv_comp, ← reassoc_of% he]; simp
  have h2 : b' ≫ d'.inv = d'.inv ≫ a' := by rw [Iso.eq_inv_comp, ← reassoc_of% hd']; simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hd, reassoc_of% h, reassoc_of% h2, he']

theorem exists_ext_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' hf hf'
  have hx := semiAbelian_hom_extends_uniquely_dvr T.V T.Fr
  have inj : ∀ (s s' : SAB H (Sp T.V)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (Over.pullback (spMap (algebraMap T.V T.Fr))).map F' →
        F = F' := by
    intro s s' F F' hF hF' h
    exact (hx s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have hpow : ∀ (s : SAB H (Sp T.V)) (N : ℕ), IsMonHom (𝟙 s.G ^ N) := by
    intro s N
    induction N with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit s.G ≫ η[s.G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 s.G ^ n) (𝟙 s.G) ≫ μ[s.G]))
  obtain ⟨d, hd, hdφ, hda⟩ := sabMap_exists_iso_pullback m₁
  obtain ⟨e, he, heφ, hea⟩ := sabMap_exists_iso_pullback m₂
  obtain ⟨d', hd', hdφ', hda'⟩ := sabMap_exists_iso_pullback n₁
  obtain ⟨e', he', heφ', hea'⟩ := sabMap_exists_iso_pullback n₂
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx G.G G'.G G.semi G'.semi
    ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) (by dsimp; infer_instance)
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx G'.G G.G G'.semi G.semi
    ((e'.symm ≪≫ d').hom ≫ f' ≫ (e.symm ≪≫ d).inv) (by dsimp; infer_instance)
  have : IsMonHom (e.symm ≪≫ d).hom := by dsimp; infer_instance
  have : IsMonHom (e'.symm ≪≫ d').hom := by dsimp; infer_instance
  refine ⟨F, F', hF, hF', ext_of_map_eq m₁ m₂ n₁ n₂ f F d d' e e' hdφ hdφ' heφ heφ' hFf,
    ext_of_map_eq n₁ n₂ m₁ m₂ f' F' d' d e' e hdφ' hdφ heφ' heφ hFf', fun N h => ?_, fun N h => ?_,
    fun h a => ?_, fun h a => ?_⟩
  · refine inj _ _ _ _ inferInstance (hpow G N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f f' N h
  · refine inj _ _ _ _ inferInstance (hpow G' N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f' f N h
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf]
    exact conj_comm e d e' d' f _ _ _ _ _ _ (hda a) (hea a) (hda' a) (hea' a) (h a)
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf']
    exact conj_comm e' d' e d f' _ _ _ _ _ _ (hda' a) (hea' a) (hda a) (hea a) (h a)

end GlobalTheory.HkIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ext_pair_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  first | exact @GlobalTheory.HkIntegral.exists_ext_pair | exact GlobalTheory.HkIntegral.exists_ext_pair | (intros; apply GlobalTheory.HkIntegral.exists_ext_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConst
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConst
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupport

variable {D : D7}

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (Matrix.transpose (y.map (cA D))))
      (T.gram.map (incA D))) x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {w r n : ℕ} (Gi : Matrix (Fin n) (Fin n) R) (Nt : Matrix (Fin n) (Fin r) R)
    (Tt : Matrix (Fin r) (Fin w) R) (GW : Matrix (Fin w) (Fin w) R) (a : Matrix (Fin w) (Fin r) R)
    (M : Matrix (Fin r) (Fin n) R) (hP : M * Gi * Nt = 1) :
    Matrix.trace (Gi * (Nt * Tt) * GW * (a * M)) = Matrix.trace (Tt * (GW * a)) := by
  rw [show Gi * (Nt * Tt) * GW * (a * M) = (Gi * Nt * Tt * GW * a) * M by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, show M * (Gi * Nt * Tt * GW * a) = (M * Gi * Nt) * (Tt * (GW * a)) by
      simp only [Matrix.mul_assoc], hP, Matrix.one_mul]

theorem adj_mul_conj {r n : ℕ} (C : Matrix (Fin n) (Fin r) D.host.E) (K : Matrix (Fin r) (Fin n) D.host.E)
    (hKC : K * C = 1) : adj D C * Matrix.transpose (K.map star) = 1 := by
  have e1 : adj D C = Matrix.conjTranspose C := rfl
  have e2 : Matrix.transpose (K.map star) = Matrix.conjTranspose K := rfl
  rw [e1, e2, ← Matrix.conjTranspose_mul, hKC, Matrix.conjTranspose_one]

theorem symplO_isoPart_restEmb (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (a t : Mx D W.rank r) :
    symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C a) (restEmb V W K t) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 *
        ∑ i, ∑ j, cA D (t i j) * (HMul.hMul (W.gram.map (incA D)) a : Mx D W.rank r) i j) := by
  rw [symplO, hO_eq_trace]
  congr 2
  have hN : (restEmb V W K t).map (cA D) =
      HMul.hMul (t.map (cA D)) ((K.map star).map (incA D)) := by
    rw [restEmb, Matrix.map_mul]
    congr 1
  have hP : HMul.hMul (HMul.hMul ((adj D C * V.gram).map (incA D)) ((V.gram⁻¹).map (incA D)))
      (Matrix.transpose ((K.map star).map (incA D))) = (1 : Matrix (Fin r) (Fin r) (AE D)) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc (adj D C),
      Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit V), Matrix.mul_one, adj_mul_conj C K hKC,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart, hN, Matrix.transpose_mul]
  rw [trace_inverseGram_conj_smul_eq _ _ _ _ _ _ hP]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem res_smul (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) :
    res V V' W C B μ 𝓨 (c • g) = c • res V V' W C B μ 𝓨 g := by
  funext x
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem res_eq_zero_of_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V' W : HSp D} {r : ℕ}
    {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : IsIsoSplit V V' C B) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W)
    {y : Mx D W.rank r} (hy : heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f = f)
    (hne : ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) ≠ 1) :
    res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  have h4 := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ hg).2.2.2 y
  rw [GlobalTheory.SplitScalar.heisO_comm, hy, res_smul] at h4
  have h5 : (ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) - 1) • res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
    rw [sub_smul, h4, one_smul, sub_self]
  exact (smul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hne)

theorem sum_single {m n : ℕ} (t : Mx D m n) (i : Fin m) (j : Fin n) (s : AE D) :
    ∑ k, ∑ l, cA D (t k l) * (Matrix.single i j s : Mx D m n) k l = cA D (t i j) * s := by
  simp [Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem continuous_isoPart_single (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (G : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (i : Fin W.rank) (j : Fin r) :
    Continuous fun s : AE D =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul G (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h1 : Continuous fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D)) := by
    have e : (fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D))) =
        fun s => s • (Matrix.single i j 1 : Matrix (Fin W.rank) (Fin r) (AE D)) := by
      funext s; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact continuous_id.smul continuous_const
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const


set_option maxHeartbeats 800000 in
theorem supp_locConst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  intro D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC _ e he f hf
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  obtain ⟨U, hUo, hU⟩ := hf.level
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  let R : halfMx (cA D e) W.rank r →+ WO V W :=
    { toFun := fun t => restEmb V W K t
      map_zero' := Matrix.zero_mul _
      map_add' := fun x y => restEmb_add V W K x y }
  have hRc : Continuous R := continuous_subtype_val.matrix_mul continuous_const

  let Gi : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (W.gram⁻¹).map (incA D)
  have hGG : HMul.hMul (W.gram.map (incA D)) Gi = (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W),
      Matrix.map_one _ (map_zero _) (map_one _)]

  have key : ∀ (i : Fin W.rank) (j : Fin r), ∃ Cij : Set (AE D), IsCompact Cij ∧ ∀ x, e * x = x →
      (∀ s ∈ (fun s : AE D => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r)) ⁻¹' (U : Set (WO V W)),
        e * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (x * s)) = 1) → x ∈ Cij := fun i j => by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j (0 : AE D) : Mx D W.rank r) : Mx D W.rank r) = 0 := by
      rw [Matrix.single_zero, Matrix.mul_zero]
      exact Matrix.zero_mul _
    refine GlobalTheory.SplitAnnihilator.annihilator_subset_compact D ψ (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) e he _ ?_
    refine (continuous_isoPart_single V W C Gi i j).continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact hUo.mem_nhds U.zero_mem
  choose Cij hCc hCm using key
  let Kij : Fin W.rank → Fin r → Set (AE D) := fun i j =>
    (fun x => cA D (incA D D.host.xi0⁻¹ * x)) '' Cij i j
  refine ⟨U.comap R, {t | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j}, hUo.preimage hRc, ?_, ?_, ?_⟩
  · have hK : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
        Set (Fin W.rank → Fin r → AE D)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
        (hCc i j).image (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp (continuous_const.mul continuous_id))
    have := (isClosed_halfMx (cA D e) W.rank r).isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have e : {t : halfMx (cA D e) W.rank r | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j} =
        Subtype.val ⁻¹' (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
          Set (Fin W.rank → Fin r → AE D)) := by
      ext t
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [e]
    exact this
  · intro t ht
    by_contra hne
    apply ht
    intro i j
    have hti : cA D e * (t : Mx D W.rank r) i j = (t : Mx D W.rank r) i j := t.2 i j
    have hti' : e * cA D ((t : Mx D W.rank r) i j) = cA D ((t : Mx D W.rank r) i j) := by
      have := congrArg (cA D) hti
      rwa [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
    refine ⟨incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j), hCm i j _ (by rw [mul_left_comm, hti']) ?_, ?_⟩
    · intro s hsU hse
      by_contra hψ1
      have ha : IsHalf e (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
        refine mul_isHalf (fun k l => ?_) Gi
        simp only [Matrix.single_apply]
        split_ifs
        · exact hse
        · exact mul_zero e
      have hfin := GlobalTheory.SplitScalar.half_fin he (isHalf_mul ha ((adj D C * V.gram).map (incA D)))
      apply hne
      refine res_eq_zero_of_ne hψ hs hμ hf _ (hU _ hsU hfin) ?_
      rw [symplO_isoPart_restEmb V W C K hKC, ← Matrix.mul_assoc, hGG, Matrix.one_mul, sum_single, ← mul_assoc]
      exact hψ1
    · show cA D (incA D D.host.xi0⁻¹ * (incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j))) = _
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D), map_one, one_mul,
        GlobalTheory.DualPairCheck.cA_cA]
  · intro t l hl
    have hl' : restEmb V W K l ∈ U := hl
    have hlh : IsHalf (cA D e) (restEmb V W K l) := isHalf_mul l.2 _
    have hth : IsHalf (cA D e) (restEmb V W K t) := isHalf_mul t.2 _
    have hfin := GlobalTheory.SplitScalar.half_fin he' hlh
    rw [AddSubgroup.coe_add, restEmb_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W
      (GlobalTheory.SplitScalar.symplO_eq_zero V W (by rw [GlobalTheory.DualPairCheck.cA_cA, he.2.1]) hth hlh), hU _ hl' hfin]

end GlobalTheory.HalfSupport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  first | exact @GlobalTheory.HalfSupport.supp_locConst | exact GlobalTheory.HalfSupport.supp_locConst | (intros; apply GlobalTheory.HalfSupport.supp_locConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantThetaPairingOfNoTensorIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantThetaPairingOfNoTensorIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairVanish

open GlobalTheory.ArchRec.PairTensor (ext_ctr exists_map)
open GlobalTheory.Chain.IoLift.UImg (sumAct sumMod sumAct_single)

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map_right {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    (g : U →ₗ[ℂ] U') (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ctr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_universal (M : GKMod r s) (a : Mat p q →ₗ[ℂ] Module.End ℂ M.V)
    (hc : ∀ Y Z, a Y * M.act Z = M.act Z * a Y) (U : Type) [AddCommGroup U] [Module ℂ U] :
    ∃ (Q : GKMod r s) (B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] Q.V), PInv a R B₀ ∧
      (∀ Z P v, B₀ (M.act Z P) v = Q.act Z (B₀ P v)) ∧
      ∀ P v, B₀ P v = 0 → ∀ B : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B → B P v = 0 := by

  obtain ⟨G, hG⟩ : ∃ G : Set (R.HK.V →₀ M.V), G =
      {x | (∃ (P : M.V) (v w : R.HK.V),
          x = Finsupp.single (v + w) P - Finsupp.single v P - Finsupp.single w P) ∨
        (∃ (P : M.V) (v : R.HK.V) (c : ℂ),
          x = Finsupp.single (c • v) P - starRingEnd ℂ c • Finsupp.single v P) ∨
        ∃ (P : M.V) (v : R.HK.V) (Z : Mat p q),
          Z ∈ upq p q ∧ x = Finsupp.single v (a Z P) + Finsupp.single (R.HK.act Z v) P} := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ (R.HK.V →₀ M.V), N = Submodule.span ℂ G := ⟨_, rfl⟩
  have hGN : ∀ x ∈ G, x ∈ N := fun x hx => hNdef ▸ Submodule.subset_span hx

  have hN : ∀ Z : Mat r s, N ≤ N.comap (sumAct M R.HK.V Z) := by
    intro Z
    conv_lhs => rw [hNdef]
    rw [Submodule.span_le]
    intro x hx
    rw [hG] at hx
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rcases hx with ⟨P, v, w, rfl⟩ | ⟨P, v, c, rfl⟩ | ⟨P, v, Y, hY, rfl⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inl ⟨M.act Z P, v, w, by simp [sumAct_single]⟩
    · refine hGN _ ?_
      rw [hG]
      exact Or.inr (Or.inl ⟨M.act Z P, v, c, by simp [sumAct_single]⟩)
    · refine hGN _ ?_
      rw [hG]
      have hcomm : a Y (M.act Z P) = M.act Z (a Y P) := LinearMap.congr_fun (hc Y Z) P
      exact Or.inr (Or.inr ⟨M.act Z P, v, Y, hY, by simp [sumAct_single, hcomm]⟩)
  let actQ : Mat r s →ₗ[ℂ] Module.End ℂ ((R.HK.V →₀ M.V) ⧸ N) :=
    { toFun := fun Z => N.mapQ N (sumAct M R.HK.V Z) (hN Z)
      map_add' := fun Z Z' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply]
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp [Submodule.mapQ_apply] }
  have hQ : ∀ Z y, actQ Z (Submodule.Quotient.mk y) = Submodule.Quotient.mk (sumAct M R.HK.V Z y) :=
    fun _ _ => rfl
  let Q : GKMod r s :=
    { V := (R.HK.V →₀ M.V) ⧸ N
      act := actQ
      lie := fun X Y => by
        have h : sumAct M R.HK.V (X * Y - Y * X) =
            sumAct M R.HK.V X * sumAct M R.HK.V Y - sumAct M R.HK.V Y * sumAct M R.HK.V X :=
          (sumMod M R.HK.V).lie X Y
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply, hQ]
        rw [h]
        simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.Quotient.mk_sub]
      kfin := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        obtain ⟨W, hW, hy, hK⟩ : ∃ W : Submodule ℂ (R.HK.V →₀ M.V), FiniteDimensional ℂ W ∧ y ∈ W ∧
            KStable (sumAct M R.HK.V) W := (sumMod M R.HK.V).kfin y
        refine ⟨W.map N.mkQ, Module.Finite.map W N.mkQ, Submodule.mem_map_of_mem hy, ?_⟩
        intro X hX w hw
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
        exact Submodule.mem_map_of_mem (hK X hX u hu)
      wts := fun x => by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
        have hy : y ∈ ⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ := (sumMod M R.HK.V).wts y
        have hle : (⨆ μ : Ix r s → ℚ, wtSub (sumAct M R.HK.V) μ).map N.mkQ ≤
            ⨆ μ : Ix r s → ℚ, wtSub actQ μ := by
          rw [Submodule.map_iSup]
          refine iSup_mono fun μ => ?_
          rw [Submodule.map_le_iff_le_comap]
          intro u hu
          rw [Submodule.mem_comap]
          simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hu ⊢
          intro i
          have hi := hu i
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hi ⊢
          rw [Submodule.mkQ_apply, hQ, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, hi,
            Submodule.Quotient.mk_zero]
        exact hle (Submodule.mem_map_of_mem hy) }
  let B₀ : M.V →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] ((R.HK.V →₀ M.V) ⧸ N) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P v => N.mkQ (Finsupp.single v P))
      (fun P P' v => by simp [Finsupp.single_add])
      (fun c P v => by
        simp only [RingHom.id_apply]
        rw [← Finsupp.smul_single, map_smul])
      (fun P v w => by
        rw [← map_add (f := _), ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inl ⟨P, v, w, by abel⟩)
      (fun c P v => by
        rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine hGN _ ?_
        rw [hG]
        exact Or.inr (Or.inl ⟨P, v, c, rfl⟩))
  refine ⟨Q, B₀, ?_, ?_, ?_⟩
  · intro Z hZ P v
    show N.mkQ (Finsupp.single v (a Z P)) + N.mkQ (Finsupp.single (R.HK.act Z v) P) = 0
    rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine hGN _ ?_
    rw [hG]
    exact Or.inr (Or.inr ⟨P, v, Z, hZ, rfl⟩)
  · intro Z P v
    show N.mkQ (Finsupp.single v (M.act Z P)) = actQ Z (N.mkQ (Finsupp.single v P))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, hQ, sumAct_single]
  · intro P v h B hB
    let L : (R.HK.V →₀ M.V) →ₗ[ℂ] U := Finsupp.lsum ℂ fun w => B.flip w
    have hL : ∀ w (P' : M.V), L (Finsupp.single w P') = B P' w := by
      intro w P'
      simp [L]
    have hNL : N ≤ LinearMap.ker L := by
      rw [hNdef, Submodule.span_le]
      intro x hx
      rw [hG] at hx
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hx with ⟨P', w, w', rfl⟩ | ⟨P', w, c, rfl⟩ | ⟨P', w, Z, hZ, rfl⟩
      · simp [hL]
      · simp [hL]
      · rw [map_add (f := _), hL, hL]
        exact hB Z hZ P' w
    have h' : N.mkQ (Finsupp.single v P) = 0 := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
    have := hNL h'
    rw [LinearMap.mem_ker, hL] at this
    exact this

theorem pairNo_of_tensNo : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁), IsGK a₁ → IsGK a₂ → (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → AdmGK R₁.HK → TensNo a₁ a₂ R₁ → PairNo a₁ R₁ := by
  intro p q r s T₁ σ a₁ a₂ R₁ h₁ h₂ hc hA hT U _ _ B hB

  let M : GKMod r s :=
    { V := MvPolynomial σ ℂ
      act := a₂
      lie := h₂.1
      kfin := h₂.2.1
      wts := h₂.2.2 }
  obtain ⟨Q, B₀, hB₀, hZ, huniv⟩ := exists_universal R₁ M a₁ hc U
  obtain ⟨f, hf, hfB⟩ := GlobalTheory.ArchRec.PairTensor.exists_map R₁ a₁ h₁ hA B₀ hB₀
  have hT' : TIntw a₁ a₂ R₁.HK Q f := by
    refine ⟨hf, fun Y => LinearMap.ext fun P => ?_⟩
    refine GlobalTheory.ArchRec.PairTensor.ext_ctr R₁ Q.V _ _ fun v => ?_
    simp only [LinearMap.comp_apply]
    rw [← hfB, ctr_map_right, ← hfB]
    exact hZ Y P v
  have hf0 : f = 0 := hT Q f hT'
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  refine huniv P v ?_ B hB
  rw [hfB, hf0, LinearMap.zero_apply, map_zero]

end GlobalTheory.ArchRec.PairVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantThetaPairingOfNoTensorIntertwinerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_invariant_theta_pairing_of_no_tensor_intertwiner : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁), IsGK a₁ → IsGK a₂ → (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → AdmGK R₁.HK → TensNo a₁ a₂ R₁ → PairNo a₁ R₁ := by
  first | exact @GlobalTheory.ArchRec.PairVanish.pairNo_of_tensNo | exact GlobalTheory.ArchRec.PairVanish.pairNo_of_tensNo | (intros; apply GlobalTheory.ArchRec.PairVanish.pairNo_of_tensNo <;> assumption)
end
end

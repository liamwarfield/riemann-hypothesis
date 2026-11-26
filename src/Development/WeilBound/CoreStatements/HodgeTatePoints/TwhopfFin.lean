module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  exact ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) f,
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) f⟩

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) f U' hU' U.ι).ge
    (Set.mem_univ ⟨x, hx⟩)

theorem mem_of_finite {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge
    (Set.mem_univ z)

theorem finite_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem mem_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) → ∀ t, (⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t) := by
  intro R _ _ _ _ T _ _ Γ U hfin hU t
  constructor
  · intro ht
    obtain ⟨σ, -, hσ⟩ := exists_section_of_generic_point R T Γ U hfin t ht
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ z _
    have key := mem_of_finite U hU (𝟙_ _) (show IsFinite (𝟙 _) from inferInstance) σ
      ((toUnit (genPt R)).left z)
    rw [← hσ]
    simpa using key


open Polynomial in
theorem exists_root_near (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    (a₀ : V) (n : ℕ) : ∀ f : V[X], f.Monic → f.natDegree = n → f.eval a₀ ∈ IsLocalRing.maximalIdeal V →
      ∃ a, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  induction n with
  | zero =>
    intro f hf hn h
    rw [hf.natDegree_eq_zero.1 hn, eval_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  | succ n ih =>
    intro f hf hn h
    have hinj := IsFractionRing.injective V (FractionRing V)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (FractionRing V) hinj f
      (by rw [degree_eq_natDegree hf.ne_zero, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨f, hf, by rwa [← aeval_def]⟩ : IsIntegral V x)
    have hr : f.IsRoot r := hinj (by rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval])
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.2 hr
    have hg : g.Monic := (monic_X_sub_C r).of_mul_monic_left hf
    rw [eval_mul] at h
    rcases (IsLocalRing.maximalIdeal.isMaximal V).isPrime.mem_or_mem h with h | h
    · refine ⟨r, hr, ?_⟩
      have := neg_mem h
      simpa using this
    · have hd : g.natDegree = n := by
        rw [(monic_X_sub_C r).natDegree_mul hg, natDegree_X_sub_C] at hn
        omega
      obtain ⟨a, ha, ha'⟩ := ih g hg hd h
      exact ⟨a, ha.dvd (dvd_mul_left _ _), ha'⟩

theorem henselian_of_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], HenselianLocalRing V := by
  intro V _ _ _ _
  exact ⟨fun f hf a₀ h _ => exists_root_near V a₀ _ f hf rfl h⟩

theorem padic_alg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  intro p _ C _ _ _ v O _ _ _ hv _ hO
  haveI := hO
  haveI hval : ValuationRing O := ValuationRing.of_integers v hv
  haveI hfr : IsFractionRing O C := hv.isFractionRing
  haveI hac : IsAlgClosed (FractionRing O) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  exact ⟨(GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1,
    henselian_of_algClosed O, inferInstance, hval, hac, hfr⟩

theorem prime_eq_bot_or_max : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O], v.Integers O → ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  intro C _ v O _ _ _ _ hv P hP
  by_cases h0 : P = ⊥
  · exact .inl h0
  right
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun x hx => ?_
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have ha : 0 < v (algebraMap O C a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 ha0))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one ha hx1
  have hd : a ∣ x ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (P.mem_of_dvd hd haP)

end PositivityTheory.HtPt.Twhopf
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem proj_mem_omHT (σ : E →+* K) {y : Ω} (hy : y ∈ D.om') : eigProj D.ρΩ σ y ∈ D.omHT σ :=
  ⟨y, hy, rfl⟩

theorem q_mem (σ : E →+* K) (x : Fin N → A) : D.q σ x ∈ D.omHT σ := by
  unfold HTChart.q
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact proj_mem_omHT D σ (h_mem_om' D _)

theorem q_add (σ : E →+* K) (x y : Fin N → A) : D.q σ (x + y) = D.q σ x + D.q σ y := by
  unfold HTChart.q
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem q_smul (σ : E →+* K) (a : A) (x : Fin N → A) : D.q σ (a • x) = a • D.q σ x := by
  unfold HTChart.q
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (z : Fin N → 𝓞 E) :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ (D.h z) = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)
  choose b hb using fun i => hσ (z i)
  have hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v := by
    intro a v
    have h1 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)
    have h2 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
    rw [h1, h2]
  refine ⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [he, map_add (f := _), hrho, ← hb, algebraMap_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_add_distrib, map_sum, Finset.smul_sum]
  unfold HTChart.q
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

theorem exists_q_add (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    {y : Ω} (hy : y ∈ D.om') :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ y = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp ht
  clear hy ht
  have key : ∃ x : Fin N → A, ∃ y' ∈ D.om,
      eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
    induction hs using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z
    | zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩
    | add u v _ _ hu hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hu
      obtain ⟨x2, y2, hy2, e2⟩ := hv
      refine ⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩
      rw [map_add (f := _), e1, e2, q_add, map_add (f := _), smul_add]
      abel
    | smul a v _ hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hv
      refine ⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩
      rw [LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]
  obtain ⟨x, y', hy', e⟩ := key
  have ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0)
      = ((p : A) ^ R) • eigProj D.ρΩ σ y0 := by
    simp [LinearMap.map_smul_of_tower]
  refine ⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩
  rw [map_add (f := _), e, ht0, map_add (f := _), smul_add, add_assoc]

end

theorem q_surj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ
  classical
  refine ⟨fun x => q_mem D σ x, ?_, ?_⟩
  · unfold HTChart.omHT eigQuot
    apply Submodule.FG.map
    unfold HTChart.om'
    refine Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)
    refine ⟨T.image D.h, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨z, _, rfl⟩ := hv
      exact ⟨z, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E)) := hT ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem w hw =>
        exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hu hv
      | smul n u _ hu =>
        rw [map_zsmul]
        exact zsmul_mem hu n
  · intro y hy
    simp only [HTChart.omHT, eigQuot] at hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, y'', hy'', e⟩ := exists_q_add D σ hσ hw
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩
    · exact Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))
    · rw [LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]
      congr 1
      simp only [smul_smul]
      congr 1
      ring

end PositivityTheory.HtPt.Ga
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Mh

section pb

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {X Y : Scheme.{0}}

def pb (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

def val (x : Spec (CommRingCat.of B) ⟶ X) : Γ(X, ⊤) →+* B :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom

theorem valAt_top (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) : valAt x ⊤ h s = val x s := by
  simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_ext {j j' : X ⟶ Spec (CommRingCat.of A)} (h : ∀ a, pb j a = pb j' a) : j = j' := by
  apply ext_of_isAffine
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j'.appTop := by
    ext a
    exact h a
  exact (cancel_epi _).1 e

theorem pb_comp (f : Y ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) : pb (f ≫ j) a = f.appTop (pb j a) := by
  unfold pb
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem val_comp (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X) (s : Γ(X, ⊤)) :
    val (x ≫ f) s = val x (f.appTop s) := by
  unfold val
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem pb_spec (j : X ⟶ Spec (CommRingCat.of B)) (ψ : A →+* B) (a : A) :
    pb (j ≫ Spec.map (CommRingCat.ofHom ψ)) a = pb j (ψ a) := by
  simp only [pb, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem val_pb_id (b : B) : val (𝟙 _) (pb (𝟙 (Spec (CommRingCat.of B))) b) = b := by
  simp [val, pb]

theorem val_pb_comp (x : Spec (CommRingCat.of B) ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    val x (pb j a) = val (𝟙 _) (pb (x ≫ j) a) := by
  rw [pb_comp, ← val_comp, Category.id_comp]

theorem val_pb {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : x ≫ j = Spec.map (CommRingCat.ofHom φ)) (a : A) : val x (pb j a) = φ a := by
  have e := pb_spec (𝟙 (Spec (CommRingCat.of B))) φ a
  rw [Category.id_comp] at e
  rw [val_pb_comp, h, e, val_pb_id]

theorem val_id_injective : Function.Injective (val (𝟙 (Spec (CommRingCat.of B)))) := by
  intro s t hst
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) s) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) t) := by
    rw [hst]
  simpa [val] using e

theorem comp_eq_spec {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : ∀ a, val x (pb j a) = φ a) : x ≫ j = Spec.map (CommRingCat.ofHom φ) := by
  refine pb_ext fun a => val_id_injective ?_
  rw [← val_pb_comp, h, val_pb (Category.id_comp _)]

theorem exists_pb (φ : A →+* Γ(X, ⊤)) : ∃ j : X ⟶ Spec (CommRingCat.of A), ∀ a, pb j a = φ a := by
  refine ⟨(ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) (CommRingCat.ofHom φ).op,
    fun a => ?_⟩
  rw [pb, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rfl

theorem spec_inj {φ ψ : A →+* B} (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

end pb

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T]

theorem sec_ext (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)} (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') :
    s = s' := by
  rw [← sub_eq_zero]
  refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
  rw [valAt_top, map_sub, h, sub_self]

theorem hom_ext_pt (Γ : QFGroup R T) {A : Type} [CommRing A] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
  pb_ext fun a => sec_ext Γ fun t => by rw [val_pb_comp, h, ← val_pb_comp]

theorem mem_top_iff (Γ : QFGroup R T) (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
    ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
  have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
      (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
    intro B _ X x U hx a b
    simp only [valAt, map_sub]
  constructor
  · intro hf t
    rw [Twhopf.mem_order] at hf
    have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
        ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
          valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
      fun g => hf t g (by simp)
    choose U hgU s hs using hreg
    obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
      (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
        intro g g'
        rw [← sub_eq_zero]
        apply Twhopf.sec_inj R T Γ _ _
        intro h hh
        have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
        have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
        refine (hsub _ _ hh _ _).trans ?_
        erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
        rw [hs, hs, sub_self])
    refine ⟨g0, fun h => ?_⟩
    have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
      Twhopf.top_le_of_mem _ z (hgU _)
    refine (valAt_top _ htop g0).symm.trans ?_
    refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
    erw [hglue ((Γ.pt h).left z)]
    exact hs _ h hh
  · intro hf
    rw [Twhopf.mem_order]
    intro t g _
    obtain ⟨s, hs⟩ := hf t
    unfold QFGroup.RegularAt
    exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩

omit [Finite T] in
theorem val_const (Γ : QFGroup R T) (t : T) (r : R) :
    val (Γ.pt t).left (pb Γ.G.hom r) = algebraMap R (FractionRing R) r :=
  val_pb (Over.w (Γ.pt t)) r

omit [Finite T] in
theorem val_emb {Γ : QFGroup R T} {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (a : A) :
    val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
  val_pb (hj.pt t) a

theorem exists_emb (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (hA : ∀ a : A, ∃ s : Γ(Γ.G.left, ⊤), ∀ t, val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t)) :
    ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of A), Γ.IsEmb A j := by
  choose s hs using hA
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := sec_ext Γ fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => sec_ext Γ fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := sec_ext Γ fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => sec_ext Γ fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hom_ext_pt Γ fun t => by rw [hj'.pt, hpt]⟩
  apply hom_ext_pt Γ
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end PositivityTheory.HtPt.Mh
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X N Q : Type} [AddCommGroup X] [AddCommGroup N] [AddCommGroup Q]

lemma map_res_eq (M : Submodule R (N → C)) (ι : X →+ N) (K : AddSubgroup N) (e : X ≃+ K)
    (he : ∀ x, (e x : N) = ι x) :
    M.map (LinearMap.funLeft R C ι) =
      (M.map (resK (R := R) K)).map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (X → C)) := by
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro g
  funext x
  show g (ι x) = g (e x)
  rw [he]

lemma comap_quo_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (K : AddSubgroup N) (e : Q ≃+ N ⧸ K)
    (he : ∀ x, e (ψ x) = (x : N ⧸ K)) :
    M.comap (LinearMap.funLeft R C ψ) =
      (M.comap (pullQ (R := R) K)).map (pbE (C := C) (R := R) e : (N ⧸ K → C) →ₗ[R] (Q → C)) := by
  ext g
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  have : pullQ (R := R) K ((pbE (C := C) (R := R) e).symm g) = LinearMap.funLeft R C ψ g := by
    funext x
    show (pbE (C := C) (R := R) e).symm g (x : N ⧸ K) = g (ψ x)
    rw [LinearEquiv.funCongrLeft_symm]
    show g (e.symm (x : N ⧸ K)) = g (ψ x)
    rw [← he, AddEquiv.symm_apply_apply]
  rw [this]

lemma exists_subEquiv (ι : X →+ N) (hι : Function.Injective ι) (K : AddSubgroup N)
    (hK : ι.range = K) : ∃ e : X ≃+ K, ∀ x, (e x : N) = ι x := by
  subst hK
  exact ⟨AddMonoidHom.ofInjective hι, fun _ => rfl⟩

lemma exists_quoEquiv (ψ : N →+ Q) (hψ : Function.Surjective ψ) (K : AddSubgroup N)
    (hK : K = ψ.ker) : ∃ e : Q ≃+ N ⧸ K, ∀ x, e (ψ x) = (x : N ⧸ K) := by
  subst hK
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm, fun x => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  rfl

lemma invFun_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (hψ : Function.Surjective ψ)
    (K : AddSubgroup N) (hK : ∀ x, x ∈ K ↔ ψ x = 0) :
    invFun M K = (M.comap (LinearMap.funLeft R C ψ)).map (LinearMap.funLeft R C ψ) := by
  ext g
  constructor
  · rintro ⟨hg, hinv⟩
    have h : LinearMap.funLeft R C ψ (fun c => g (Function.surjInv hψ c)) = g := by
      funext x
      show g (Function.surjInv hψ (ψ x)) = g x
      have hk : Function.surjInv hψ (ψ x) - x ∈ K := by
        rw [hK, map_sub, Function.surjInv_eq hψ, sub_self]
      have := hinv x _ hk
      rwa [add_sub_cancel] at this
    exact ⟨_, by show LinearMap.funLeft R C ψ _ ∈ M; rw [h]; exact hg, h⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q (ψ (x + k)) = q (ψ x)
    rw [map_add (f := _), (hK k).1 hk, add_zero]

lemma aug_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ augIdeal M) :
    LinearMap.funLeft R C φ g ∈ augIdeal M' := by
  rw [mem_aug] at hg ⊢
  refine ⟨h g hg.1, ?_⟩
  show g (φ 0) = 0
  rw [map_zero, hg.2]

lemma sq_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    LinearMap.funLeft R C φ g ∈ sqIdeal (augIdeal M') := by
  have h' : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C φ) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro s ⟨f, hf, f', hf', rfl⟩
    exact Submodule.subset_span ⟨_, aug_pull φ M M' h hf, _, aug_pull φ M M' h hf', rfl⟩
  exact h' (Submodule.mem_map_of_mem hg)

variable {v : Valuation C NNReal}

theorem exists_res (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype X] [DecidableEq X]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι) :
    ∃ AK : HopfOrder (C := C) R X, AK.carrier = AA.carrier.map (LinearMap.funLeft R C ι) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hK
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨AK, hAK⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N K AA
  refine ⟨hopfPull e AK, ?_⟩
  rw [map_res_eq _ ι _ e he, ← hAK]
  rfl

theorem exists_quo (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ψ : N →+ Q) (hψ : Function.Surjective ψ) :
    ∃ AQ : HopfOrder (C := C) R Q, AQ.carrier = AA.carrier.comap (LinearMap.funLeft R C ψ) := by
  classical
  obtain ⟨e, he⟩ := exists_quoEquiv ψ hψ ψ.ker rfl
  have : Fintype (N ⧸ ψ.ker) := Fintype.ofFinite _
  obtain ⟨-, ⟨AQ, hAQ⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N ψ.ker AA
  refine ⟨hopfPull e AQ, ?_⟩
  rw [comap_quo_eq _ ψ _ e he, ← hAQ]
  rfl

theorem colen_ses [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hex : ι.range = ψ.ker) (c cQ cK : NNReal)
    (hc : HasColen R v AA.carrier c)
    (hQ : HasColen R v (AA.carrier.comap (LinearMap.funLeft R C ψ)) cQ)
    (hK : HasColen R v (AA.carrier.map (LinearMap.funLeft R C ι)) cK) :
    c = cQ ^ Fintype.card X * cK ^ Fintype.card Q := by
  classical
  obtain ⟨K, hKd⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hKd
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ K (hKd ▸ hex)
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨-, -, h3iii, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  rw [map_res_eq _ ι _ e he] at hK
  rw [comap_quo_eq _ ψ _ e' he'] at hQ
  have hK' := hasColen_map v e.symm _ _ hK
  have hQ' := hasColen_map v e'.symm _ _ hQ
  rw [map_pbE_symm] at hK' hQ'
  rw [Fintype.card_congr e.toEquiv, Fintype.card_congr e'.toEquiv]
  exact h3iii c cQ cK hc hQ' hK'

theorem om_exact [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hι : Function.Injective ι) (hex : ι.range = ψ.ker)
    (g : N → C) (hg : g ∈ augIdeal AA.carrier)
    (hr : LinearMap.funLeft R C ι g ∈
      sqIdeal (augIdeal (AA.carrier.map (LinearMap.funLeft R C ι)))) :
    ∃ b ∈ augIdeal (AA.carrier.comap (LinearMap.funLeft R C ψ)),
      g - LinearMap.funLeft R C ψ b ∈ sqIdeal (augIdeal AA.carrier) := by
  classical
  obtain ⟨e, he⟩ := exists_subEquiv ι hι _ rfl
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ ι.range hex
  have : Fintype (N ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨-, -, -, h3iv⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N ι.range AA
  have hres : ∀ f : N → C, LinearMap.funLeft R C (e.symm : ι.range →+ X)
      (LinearMap.funLeft R C ι f) = resK (R := R) ι.range f := by
    intro f
    funext k
    show f (ι (e.symm k)) = f k
    rw [← he, AddEquiv.apply_symm_apply]
  have h1 := sq_pull (e.symm : ι.range →+ X) _ (AA.carrier.map (resK (R := R) ι.range))
    (by rintro _ ⟨f, hf, rfl⟩; rw [hres]; exact ⟨f, hf, rfl⟩) hr
  rw [hres, sq_eq_mul] at h1
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (h3iv g hg h1)
  obtain ⟨b, hb, rfl⟩ := hu
  have hp : ∀ b : N ⧸ ι.range → C, LinearMap.funLeft R C ψ
      (LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b) = pullQ (R := R) ι.range b := by
    intro b
    funext x
    show b (e' (ψ x)) = b x
    rw [he']
  refine ⟨LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b, aug_pull _ _ _ ?_ hb, ?_⟩
  · intro f hf
    show LinearMap.funLeft R C ψ _ ∈ AA.carrier
    rw [hp]
    exact hf
  · rw [hp, ← huw, add_sub_cancel_left, sq_eq_mul]
    exact hw

end Gen

section Scalars

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
variable {X N : Type} [AddCommGroup X] [AddCommGroup N] [Module F X] [Module F N]

lemma fstable_map (M : Submodule R (N → C)) (hM : FStable (F := F) M) (ι : X →ₗ[F] N) :
    FStable (F := F) (M.map (LinearMap.funLeft R C ι)) := by
  rintro a _ ⟨g, hg, rfl⟩
  refine ⟨_, hM a g hg, ?_⟩
  funext x
  show g (a • ι x) = g (ι (a • x))
  rw [map_smul]

lemma fstable_comap (M : Submodule R (N → C)) (hM : FStable (F := F) M) (ψ : N →ₗ[F] X) :
    FStable (F := F) (M.comap (LinearMap.funLeft R C ψ)) := by
  intro a g hg
  have := hM a _ hg
  show LinearMap.funLeft R C ψ _ ∈ M
  convert this using 1
  funext x
  show g (a • ψ x) = g (ψ (a • x))
  rw [map_smul]

lemma range_subtype_eq (K : Submodule F N) :
    (K.subtype.toAddMonoidHom).range = (K.mkQ.toAddMonoidHom).ker := by
  ext x
  simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]

end Scalars

theorem subquo : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨AK, hAK⟩ := exists_res hv AA K.subtype.toAddMonoidHom Subtype.val_injective
    exact ⟨AK, hAK, hAK ▸ fstable_map _ hAA K.subtype⟩
  · obtain ⟨AQ, hAQ⟩ := exists_quo hv AA K.mkQ.toAddMonoidHom K.mkQ_surjective
    exact ⟨AQ, hAQ, hAQ ▸ fstable_comap _ hAA K.mkQ⟩
  · exact invFun_eq _ K.mkQ.toAddMonoidHom K.mkQ_surjective _ (fun x => by simp)
  · intro c cQ cK hc hQ hK
    exact colen_ses hv AA K.subtype.toAddMonoidHom Subtype.val_injective K.mkQ.toAddMonoidHom
      K.mkQ_surjective (range_subtype_eq K) c cQ cK hc hQ hK

end PositivityTheory.HtPt.Rc
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfSub
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := PositivityTheory.HtPt.Twhopf.sub_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact PositivityTheory.HtPt.Twhopf.ind_hopf R T H H.subtype H.subtype_injective A hA

theorem PositivityTheory.HtPt.Htat.bt_sub_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) :=
  @PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GcDescend
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem test_descend : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L := by
  intro A K _ _ _ _ _ _ _ C _ v O _ _ hv _ q M _ _ L x hq h1 hinj hcen hx
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  haveI := dvr_of_height_one q h1
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap A O s) := fun s => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact le_antisymm (hv.map_le_one _) (not_lt.1 fun h => s.2 ((hcen s).2 h))
  let R := Localization.AtPrime q
  letI : Algebra R O := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  have hcomp : ∀ a : A, algebraMap R O (algebraMap A R a) = algebraMap A O a := fun a =>
    IsLocalization.lift_eq hu a
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have hinjR : Function.Injective (algebraMap R O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have h2 : algebraMap A O a = 0 := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul]
      simp only at hr
      rw [hr, zero_mul]
    have : a = 0 := hinj (by simpa using h2)
    simp [this]
  haveI : IsLocalHom (algebraMap R O) := ⟨fun r hr => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    simp only at hr ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R q]
    have h2 : IsUnit (algebraMap A O a) := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul, hcomp]
      exact hr.mul (hu s)
    rw [hv.isUnit_iff_valuation_eq_one] at h2
    intro ha
    exact ((hcen a).1 ha).ne h2⟩
  haveI : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hinjR
  haveI : Module.Flat R O := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  haveI : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h0 : (1 : O) ⊗ₜ[A] (L.mkQ x) = 0 := by
    have : Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) ≤
        LinearMap.ker (L.mkQ.baseChange O) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [(Submodule.Quotient.mk_eq_zero L).2 hy]
    simpa using this hx
  have h2 : (1 : O) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] (L.mkQ x)) = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A R O O (M ⧸ L)).injective
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
    (TensorProduct.mk A R (M ⧸ L) 1)).1 h2
  refine ⟨s, s.2, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact hs

end PositivityTheory.HtPt.Gc
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped nonZeroDivisors

theorem isFractionRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsFractionRing O C := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hv.hom_inj
  refine IsFractionRing.of_field O C fun z => ?_
  obtain ⟨a, h | h⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap z
  · exact ⟨a, 1, by simp [h]⟩
  · exact ⟨1, a, by simp [← h]⟩

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (M : Submodule A Ω) (hM : M.IsFullLattice K) : finrank A M = finrank K Ω := by
  haveI : IsLocalizedModule A⁰ M.subtype :=
    { map_units := fun s => by
        rw [← (Algebra.lsmul A (A := K) A Ω).commutes]
        exact (IsLocalization.map_units K s).map _
      surj := fun y => by
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K (M : Set Ω) y
          (by rw [hM.span_eq_top]; trivial)
        rw [Submodule.span_eq] at ht
        exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.val_injective h]⟩ }
  rw [← IsLocalizedModule.finrank_eq A⁰ M.subtype le_rfl]
  exact (IsLocalization.finrank_eq K A⁰ le_rfl).symm

theorem rankAtStalk_eq_finrank {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) : rankAtStalk M p = finrank A M := by
  have hp : p.asIdeal.primeCompl ≤ A⁰ := p.asIdeal.primeCompl_le_nonZeroDivisors
  rw [rankAtStalk, IsLocalization.finrank_eq _ p.asIdeal.primeCompl hp,
    IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp]

theorem finrank_baseChange_flat {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    [Algebra A O] (M : Type) [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.Finite A M] :
    finrank O (O ⊗[A] M) = finrank A M := by
  rw [← rankAtStalk_eq_finrank (O ⊗[A] M) (⊥ : PrimeSpectrum O), rankAtStalk_baseChange,
    rankAtStalk_eq_finrank]

theorem exists_lift {A O : Type} [CommRing A] [CommRing O] [Algebra A O] {M : Type} [AddCommGroup M]
    [Module A M] {Ω' : Type} [AddCommGroup Ω'] [Module O Ω'] (ι : M →ₛₗ[algebraMap A O] Ω') :
    ∃ j : O ⊗[A] M →ₗ[O] Ω', (∀ x, j (1 ⊗ₜ x) = ι x) ∧
      LinearMap.range j = Submodule.span O (Set.range ι) := by
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι, map_smul' := fun a x => ι.map_smulₛₗ a x }
  refine ⟨f.liftBaseChange O, fun x => by simp [f], ?_⟩
  rw [LinearMap.range_liftBaseChange]
  rfl

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsFullLattice K → Module.Projective A M → L.IsFullLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hP hL hspan hrk
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := isFractionRing_of_integers hv
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  obtain ⟨j, hj, hr⟩ := exists_lift ι
  rw [hspan] at hr
  refine ⟨j, ?_, hr, hj⟩
  have h1 : finrank O (O ⊗[A] M) = finrank O (LinearMap.range j) := by
    rw [finrank_baseChange_flat, finrank_lattice M hM, hr, finrank_lattice L hL, hrk]
  have h2 := j.rank_range_add_rank_ker
  haveI : Module.Finite O (LinearMap.range j) := inferInstance
  rw [← finrank_eq_rank O (O ⊗[A] M), ← finrank_eq_rank O (LinearMap.range j), h1] at h2
  have h3 : Module.rank O (LinearMap.ker j) = 0 := by
    rw [add_comm] at h2
    exact (Cardinal.add_nat_inj _).1 (h2.trans (zero_add _).symm)
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.rank_eq_zero).1 h3

end PositivityTheory.HtPt.Gb
end
end

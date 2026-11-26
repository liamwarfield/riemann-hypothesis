module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem ringKrullDim_le_of_hasGoingDown {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Algebra.HasGoingDown A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  obtain ⟨P, -, hP, hlo⟩ := (maximalIdeal B).exists_ideal_le_liesOver_of_le
    (p := l.last.asIdeal) (q := maximalIdeal A) (le_maximalIdeal l.last.2.ne_top)
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  exact le_iSup_of_le L (by rw [hlen])

theorem IsRegularLocalRing.of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [IsRegularLocalRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← h]
  calc (((maximalIdeal A).map (algebraMap A B)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal A).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing
    _ = ringKrullDim A := (isRegularLocalRing_iff A).mp inferInstance
    _ ≤ ringKrullDim B := ringKrullDim_le_of_hasGoingDown

theorem isRegularLocalRing_localization_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  apply IsRegularLocalRing.of_flat_of_map_maximalIdeal (A := Localization.AtPrime p)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hmap

theorem isRegularRing_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth (R := k) (S := A)
  obtain ⟨f, hfs, hfq⟩ : ∃ f ∈ s, f ∉ q := by
    by_contra! hc
    exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
  obtain ⟨q', hq', hcomap⟩ : ∃ q' : Ideal (Localization.Away f), q'.IsPrime ∧
      q'.comap (algebraMap A (Localization.Away f)) = q := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) f).mpr hfq
    exact ⟨q.map (algebraMap A (Localization.Away f)),
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ q hq hdisj,
      IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ hq hdisj⟩
  subst hcomap
  suffices IsRegularLocalRing (Localization.AtPrime q') from
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q').toRingEquiv.symm
  have hf := hstd f hfs
  obtain ⟨n, g, -, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap k (Localization.Away f))
    (RingHom.isStandardSmooth_algebraMap.mpr hf)
  algebraize [g]
  exact isRegularLocalRing_localization_of_etale (P := MvPolynomial (Fin n) k) q'

theorem isRegularLocalRing_localization_of_smooth (k A : Type*) [CommRing k] [IsRegularRing k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  have := isRegularRing_of_smooth k A
  inferInstance

theorem isRegularRing_of_smooth_field (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsRegularRing A :=
  isRegularRing_of_smooth k A

open AlgebraicGeometry CategoryTheory

theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {R : CommRingCat.{u}} [IsRegularRing R]
    (f : X ⟶ Spec R) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsm : (f.appLE ⊤ U (by simp)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have : IsRegularRing Γ(Spec R, ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  set P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hreg : IsRegularLocalRing (Localization.AtPrime P) :=
    isRegularLocalRing_localization_of_smooth Γ(Spec R, ⊤) Γ(X, U) P
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, U)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv

theorem isRegularLocalRing_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth f x

theorem isDomain_stalk_of_smooth_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsDomain (X.presheaf.stalk x) :=
  have := isRegularLocalRing_stalk_of_smooth_field f x
  IsRegularLocalRing.isDomain

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.Cartan
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.InjectiveCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

lemma discPresheaf_isSheaf (A : X → AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (discPresheaf A) := by
  have h := TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)
  have := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) (discPresheaf A)).2
  exact this h

noncomputable def germSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨discPresheaf (fun x => F.presheaf.stalk x), discPresheaf_isSheaf _⟩

noncomputable def toGerms (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ discPresheaf (fun x => F.presheaf.stalk x) where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ W.unop x.1 x.2 s
      map_zero' := by funext x; simp
      map_add' := fun s t => by funext x; simp }
  naturality W W' h := by
    ext s
    funext x
    exact F.presheaf.germ_res_apply h.unop x.1 x.2 s

lemma toGerms_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : (Opens X)ᵒᵖ) :
    Function.Injective ((toGerms F).app W) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F W.unop s t
  intro x hx
  exact congrFun h ⟨x, hx⟩

noncomputable def toGermSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F ⟶ germSheaf F :=
  ObjectProperty.homMk (toGerms F)

instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (toGermSheaf F) := by
  have : ∀ W, Mono ((toGerms F).app W) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).2 (toGerms_injective F W)
  have : Mono (toGermSheaf F).hom := NatTrans.mono_of_mono_app (toGerms F)
  exact Sheaf.Hom.mono_of_presheaf_mono (f := toGermSheaf F)

theorem cechAcyclic_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I]
    {ι : Type w} (U : ι → Opens X) : CechAcyclic I.obj U := by
  let r := Injective.factorThru (𝟙 I) (toGermSheaf I)
  have hr : toGermSheaf I ≫ r = 𝟙 I := Injective.comp_factorThru _ _
  have hr' : toGerms I ≫ r.hom = 𝟙 I.obj := congrArg (fun f => f.hom) hr
  exact CechAcyclic.of_retract (U := U) (toGerms I) r.hom hr' (cechAcyclic_discPresheaf U _)

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

section

variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

lemma res_congr {n : ℕ} (σ : Cochain P U n) {j₁ j₂ : Fin (n + 1) → ι} (h : j₁ = j₂)
    {V : Opens X} (h₁ : V ≤ inter U j₁) (h₂ : V ≤ inter U j₂) :
    res P h₁ (σ j₁) = res P h₂ (σ j₂) := by
  subst h
  rfl

lemma le_inter_const {n : ℕ} (a : ι) : U a ≤ inter U (fun _ : Fin n => a) := by
  intro x hx
  rw [mem_inter_iff]
  exact fun _ => hx

lemma inter_succ {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by
  ext x
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_inter_iff, Fin.forall_fin_succ, Function.comp]

lemma d_zero_apply (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

def constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) : Cochain P U 0 :=
  fun i => res P ((inter_le U i 0).trans (hUV (i 0))) s

lemma d_constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by
  funext i
  rw [d_zero_apply]
  simp only [constCochain, res_res, sub_self]
  rfl

end

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)


include hP in
lemma exists_glue {ι : Type w} (U : ι → Opens X) (V : Opens X) (hUV : ∀ a, U a ≤ V)
    (hV : V ≤ iSup U) (τ : Cochain P U 0) (hτ : d P U 0 τ = 0) :
    ∃ t : P.obj (op V), ∀ i : Fin 1 → ι,
      res P ((inter_le U i 0).trans (hUV (i 0))) t = τ i := by
  let sf : ∀ j, P.obj (op (U j)) := fun j => res P (le_inter_const U j) (τ (fun _ => j))
  have compat : TopCat.Presheaf.IsCompatible P U sf := by
    intro i j
    have h := congrFun hτ ![i, j]
    rw [d_zero_apply] at h
    have hle : U i ⊓ U j ≤ inter U ![i, j] := by
      intro x hx
      rw [mem_inter_iff]
      intro a
      fin_cases a
      · exact hx.1
      · exact hx.2
    rw [Pi.zero_apply] at h
    have h' := congrArg (res P hle) h
    rw [map_sub, res_res, res_res, map_zero, sub_eq_zero] at h'
    have e0 : (![i, j] ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j := by
      funext a; fin_cases a; rfl
    have e1 : (![i, j] ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i := by
      funext a; fin_cases a; rfl
    rw [res_congr P U τ e0 _ ((inf_le_right).trans (le_inter_const U j)),
      res_congr P U τ e1 _ ((inf_le_left).trans (le_inter_const U i))] at h'
    change res P inf_le_left (sf i) = res P inf_le_right (sf j)
    simp only [sf, res_res]
    exact h'.symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    U V (fun a => homOfLE (hUV a)) hV sf compat
  refine ⟨t, fun i => ?_⟩
  have hi : (fun _ : Fin 1 => i 0) = i := funext fun a => by rw [Subsingleton.elim a 0]
  have ht' : res P (hUV (i 0)) t = sf (i 0) := ht (i 0)
  rw [← res_res P (inter_le U i 0) (hUV (i 0)), ht']
  simp only [sf, res_res]
  exact (res_congr P U τ hi _ le_rfl).trans (res_refl _ _ _)


variable {P} in
lemma CechAcyclic.of_shortExact' {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ
  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ
  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ
  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc
  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]

section

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

include hS in
lemma app_injective_of_shortExact (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have : Mono S.f := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this W)

include hS in
lemma app_exact_of_shortExact (W : Opens X) (y : S.X₂.obj.obj (op W))
    (hy : S.g.hom.app (op W) y = 0) : ∃ x, S.f.hom.app (op W) x = y :=
  TopCat.Sheaf.sections_exact_of_left_exact hS.1 hS.2 y hy

set_option backward.isDefEq.respectTransparency false in
lemma comp_hom_eq_zero : S.f.hom ≫ S.g.hom = 0 := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, S.zero]
  rfl

lemma app_comp_apply_eq_zero (W : (Opens X)ᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, comp_hom_eq_zero]
  rfl

end

variable (B : Opens X → Prop)

def CechCondition (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), (∀ a, B (U a)) → iSup U = V →
    CechAcyclic F.obj U

variable {B}

lemma inter_mem (hinf : ∀ V W, B V → B W → B (V ⊓ W)) {ι : Type w} (U : ι → Opens X)
    (hU : ∀ a, B (U a)) {n : ℕ} (i : Fin (n + 1) → ι) : B (inter U i) := by
  induction n with
  | zero =>
    have : inter U i = U (i 0) := le_antisymm (inter_le U i 0) (by
      intro x hx
      rw [mem_inter_iff]
      intro a
      rwa [Fin.fin_one_eq_zero a])
    rw [this]
    exact hU _
  | succ n ih =>
    rw [inter_succ]
    exact hinf _ _ (hU _) (ih _)

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsLocallyFactorial (X : Scheme.{u}) : Prop where
  ufm_stalk : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

variable {X : Scheme.{u}}

instance (priority := 100) IsLocallyFactorial.isNormalScheme [IsIntegral X]
    [IsLocallyFactorial X] : IsNormalScheme X where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have := IsLocallyFactorial.ufm_stalk (X := X) x
    infer_instance

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]


omit [IsLocallyNoetherian X] [IsNormalScheme X] in
lemma heightOneSpectrum_eq (x : PrimeDivisor X)
    (w : HeightOneSpectrum (X.presheaf.stalk x.point)) : w = x.heightOneSpectrum := by
  have := x.dimensionLEOne_stalk
  have hmax : w.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime
  ext1
  exact IsLocalRing.eq_maximalIdeal hmax

lemma ord_nonneg_iff (x : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ x.ord f ↔ f ∈ (algebraMap (X.presheaf.stalk x.point) X.functionField).range := by
  have := x.isDedekindDomain_stalk
  have hv0 : x.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1 := by
    simp only [ord, Left.nonneg_neg_iff]
    rw [WithZero.log_le_iff_le_exp hv0]
    simp
  rw [key]
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    rw [x.heightOneSpectrum_eq w]
    exact h
  · rintro ⟨a, rfl⟩
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

end PrimeDivisor

section Algebra

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

end Algebra

section Hartogs

end Hartogs

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)


variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

end Affine

section Uniformizer

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Uniformizer

section LocallyPrincipal

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end LocallyPrincipal

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal RingTheory.Sequence

universe u

variable {R : Type u} [CommRing R]

theorem exists_isRegular_ofList_eq_maximalIdeal [IsRegularLocalRing R] :
    ∃ rs : List R, IsRegular R rs ∧ ofList rs = maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → ∃ rs : List S, IsRegular S rs ∧
        ofList rs = maximalIdeal S ∧ (rs.length : WithBot ℕ∞) = ringKrullDim S from H _ R rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hbot : maximalIdeal S = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hn
    refine ⟨[], IsRegular.nil S S, by simp [hbot], ?_⟩
    rw [← (isRegularLocalRing_iff S).mp inferInstance, hn]
    simp
  | succ n ih =>
    intro S _ _ hn
    have := IsRegularLocalRing.isDomain (R := S)
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      rw [this] at hn; simp at hn
    obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
    have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hB : (maximalIdeal (S ⧸ span {x})).spanFinrank = n := by
      have h1 := (isRegularLocalRing_iff S).mp inferInstance
      have h2 := (isRegularLocalRing_iff (S ⧸ span {x})).mp hreg
      rw [← h1, ← h2, hn] at hdim
      have : ((maximalIdeal (S ⧸ span {x})).spanFinrank + 1 : ℕ) = n + 1 := by exact_mod_cast hdim
      omega
    obtain ⟨rsB, hrsB, hofB, hlenB⟩ := ih (S ⧸ span {x}) hB
    let lift : S ⧸ span {x} → S := Function.surjInv Ideal.Quotient.mk_surjective
    have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
      Function.surjInv_eq Ideal.Quotient.mk_surjective
    let rs' := rsB.map lift
    have hmap : rs'.map (Ideal.Quotient.mk (span {x})) = rsB := by
      simp [rs', List.map_map, Function.comp_def, hlift]
    refine ⟨x :: rs', ?_, ?_, ?_⟩
    · rw [isRegular_cons_iff']
      refine ⟨?_, ?_⟩
      · exact fun a b h ↦ mul_left_cancel₀ hx0 h
      · rw [hmap]
        have e0 : QuotSMulTop x S ≃ₗ[S] S ⧸ span {x} :=
          Submodule.quotEquivOfEq _ _ (by
            rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
        let e : QuotSMulTop x S ≃ₗ[S ⧸ span {x}] S ⧸ span {x} :=
          LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e0
        exact (e.isRegular_congr rsB).mpr hrsB
    · have h1 : (ofList rs').map (Ideal.Quotient.mk (span {x})) =
          (maximalIdeal S).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_ofList, hmap, hofB,
          map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) h1
      simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h2
      rw [ofList_cons, sup_comm, h2, sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr hx)]
    · rw [List.length_cons, List.length_map, ← hdim, ← hlenB]
      push_cast
      rfl

open CategoryTheory Abelian

theorem hasProjectiveDimensionLT_of_forall_prime [IsNoetherianRing R] (n : ℕ) (I : Ideal R)
    (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ q)) n)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  revert hM
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    with
  | subsingleton N =>
    intro _
    have : Limits.IsZero (ModuleCat.of R N) := ModuleCat.isZero_of_subsingleton _
    have := this.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le _)
  | quotient N p e =>
    intro hN
    have hle : I ≤ p.1 := by
      intro a ha
      have h := congrArg e (hN a ha (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    have := hI p.1 p.2 hle
    exact hasProjectiveDimensionLT_of_iso e.symm.toModuleIso n
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    have k₁ : ∀ a ∈ I, ∀ m : N₁, a • m = 0 := fun a ha m ↦ hf (by rw [map_smul, hN a ha, map_zero])
    have k₃ : ∀ a ∈ I, ∀ m : N₃, a • m = 0 := fun a ha m ↦ by
      obtain ⟨m, rfl⟩ := hg m
      rw [← map_smul, hN a ha, map_zero]
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero f g (LinearMap.ext fun x ↦ hfg.apply_apply_eq_zero x))
      hfg hf hg
    exact hS.hasProjectiveDimensionLT_X₂ n (h₁ k₁) (h₃ k₃)

theorem hasProjectiveDimensionLT_residueField [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) :
    HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) := by
  obtain ⟨rs, hreg, hof, hlen⟩ := exists_isRegular_ofList_eq_maximalIdeal (R := R)
  have hrs : rs.length = d := by rw [hd] at hlen; exact_mod_cast hlen
  have h := ModuleCat.projectiveDimension_quotient_eq_length.{u} (R := R) rs hreg
  have h' : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ ofList rs))) d :=
    (projectiveDimension_le_iff _ d).mp (by rw [h, hrs])
  let e : Shrink.{u} (R ⧸ ofList rs) ≃ₗ[R] R ⧸ maximalIdeal R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hof)
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)


set_option backward.isDefEq.respectTransparency false in
theorem hasProjectiveDimensionLT_of_residueField [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by
  have hprime : ∀ p : Ideal R, p.IsPrime →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ p)) (n + 1) := by
    intro p
    induction p using WellFoundedGT.induction with
    | _ p ih =>
    intro hp
    by_cases hpm : p = maximalIdeal R
    · subst hpm; exact hk
    · have hlt : p < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm
      obtain ⟨x, hxm, hxp⟩ := Set.exists_of_ssubset hlt
      let N := R ⧸ p
      have hx0 : Ideal.Quotient.mk p x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have reg : IsSMulRegular N x := by
        intro a b h
        simp only [Algebra.smul_def] at h
        exact mul_left_cancel₀ hx0 h
      have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R N) reg
      have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x N)) (n + 1) := by
        refine hasProjectiveDimensionLT_of_forall_prime (n + 1) (p ⊔ span {x}) ?_ _ ?_
        · intro q hq hle
          exact ih q (lt_of_le_of_ne (le_sup_left.trans hle) (fun h ↦ hxp (h ▸
            hle (le_sup_right (a := p) ((span_singleton_le_iff_mem _).mp le_rfl))))) hq
        · intro a ha m
          have hann : p ⊔ span {x} ≤ Module.annihilator R (QuotSMulTop x N) := by
            refine sup_le ?_ ((span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator N x))
            intro b hb
            rw [Module.mem_annihilator]
            intro m
            obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
            obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
            rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
              Ideal.Quotient.eq_zero_iff_mem.mpr (p.mul_mem_right m hb), map_zero]
          exact Module.mem_annihilator.mp (hann ha) m
      apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton
        (ModuleCat.of R (QuotSMulTop x N)) (n + 1) (n + 2) (by omega) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : (ModuleCat.smulShortComplex (ModuleCat.of R N) x).f = x • 𝟙 (ModuleCat.of R N) := rfl
      simp only [this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext (ModuleCat.of R N) L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) hxm
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  exact hasProjectiveDimensionLT_of_forall_prime (n + 1) ⊥ (fun q hq _ ↦ hprime q hq) M
    (fun a ha m ↦ by rw [(Submodule.mem_bot R).mp ha, zero_smul])

theorem hasProjectiveDimensionLT_of_isRegularLocalRing [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) :=
  hasProjectiveDimensionLT_of_residueField d (hasProjectiveDimensionLT_residueField hd) M

end GroundTheory.Arith.SchemeCoh
end

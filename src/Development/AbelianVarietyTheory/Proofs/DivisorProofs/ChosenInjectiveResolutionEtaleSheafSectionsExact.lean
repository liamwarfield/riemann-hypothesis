module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

abbrev secEvalFun (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem injectiveResolution_sections_degree_zero_kernel (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ w : Sec ((injectiveResolution F).cocomplex.X 0) U,
      Sec.map ((injectiveResolution F).cocomplex.d 0 1) w = 0 →
        ∃ a : Sec F U, Sec.map ((injectiveResolution F).ι.f 0) a = w) ∧
    Function.Injective (Sec.map ((injectiveResolution F).ι.f 0) (U := U)) := by
  set I := injectiveResolution F
  have hlim := KernelFork.mapIsLimit _ I.isLimitKernelFork (secEvalFun R U)
  let S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
    ShortComplex.mk ((secEvalFun R U).map (I.ι.f 0)) ((secEvalFun R U).map (I.cocomplex.d 0 1))
      (by rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero])
  have hS : S.Exact := S.exact_of_f_is_kernel hlim
  refine ⟨fun w hw => (ShortComplex.moduleCat_exact_iff S).1 hS w hw, ?_⟩
  have : Mono ((secEvalFun R U).map (I.ι.f 0)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem chosenInjectiveResolutionAugmentation_eq_iota_comp (R : Type) [CommRing R] (F : Shv R) :
    resι R F = (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

theorem chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq (R : Type) [CommRing R] (F : Shv R) :
    (res R F).d 0 1 = ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
      (injectiveResolution F).cocomplex.d 0 1 ≫ ((injectiveResolution F).cochainComplexXIso 1 1 rfl).inv :=
  InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl

theorem chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n ≠ 0) : (res R F).ExactAt n := by
  have h : ((CochainComplex.singleFunctor (Shv R) 0).obj F).ExactAt n :=
    HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 F n hn
  exact (quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n h).1 inferInstance

theorem resSec (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧
    Function.Injective (Sec.map (resι R F) (U := U)) ∧
    (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k →
      Sec.map ((res R F).d n k) z = 0 →
        Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧
    ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  obtain ⟨hker, hinj⟩ := injectiveResolution_sections_degree_zero_kernel R F U
  set I := injectiveResolution F
  set e0 := I.cochainComplexXIso 0 0 rfl
  set e1 := I.cochainComplexXIso 1 1 rfl
  have hι : ∀ a : Sec F U, Sec.map (resι R F) a = Sec.map e0.inv (Sec.map (I.ι.f 0) a) := by
    intro a; rw [chosenInjectiveResolutionAugmentation_eq_iota_comp]; rfl
  have hd : ∀ z : Sec ((res R F).X 0) U,
      Sec.map ((res R F).d 0 1) z = Sec.map e1.inv (Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z)) := by
    intro z; rw [chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq]; rfl
  have he0 : ∀ z : Sec ((res R F).X 0) U, Sec.map e0.inv (Sec.map e0.hom z) = z := by
    intro z; change Sec.map (e0.hom ≫ e0.inv) z = z; rw [e0.hom_inv_id]; rfl
  have he0' : ∀ w : Sec (I.cocomplex.X 0) U, Sec.map e0.hom (Sec.map e0.inv w) = w := by
    intro w; change Sec.map (e0.inv ≫ e0.hom) w = w; rw [e0.inv_hom_id]; rfl
  have he1 : ∀ w : Sec (I.cocomplex.X 1) U, Sec.map e1.hom (Sec.map e1.inv w) = w := by
    intro w; change Sec.map (e1.inv ≫ e1.hom) w = w; rw [e1.inv_hom_id]; rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hd] at hz
    have hz' : Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z) = 0 := by
      have := congrArg (Sec.map e1.hom) hz
      rw [he1] at this
      exact this.trans (map_zero (e1.hom.hom.app (op U)).hom)
    obtain ⟨a, ha⟩ := hker _ hz'
    exact ⟨a, by rw [hι, ha, he0]⟩
  · rintro ⟨a, rfl⟩
    rw [hd, hι, he0']
    change Sec.map e1.inv (Sec.map (I.ι.f 0 ≫ I.cocomplex.d 0 1) a) = 0
    rw [I.ι_f_zero_comp_complex_d]
    exact map_zero _
  · intro a b hab
    rw [hι, hι] at hab
    have := congrArg (Sec.map e0.hom) hab
    rw [he0', he0'] at this
    exact hinj this
  · intro m n k hn hmn z hnk hz
    have hex : ((res R F).sc' m n k).Exact :=
      (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1
        (chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero R F n (by omega))
    exact (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R ((res R F).sc' m n k)).1 hex U z hz
  · intro n hn
    haveI : (res R F).IsStrictlyGE 0 := (inferInstance : I.cochainComplex.IsStrictlyGE 0)
    have h0 : IsZero ((res R F).X n) := CochainComplex.isZero_of_isStrictlyGE _ 0 n hn
    exact ModuleCat.isZero_iff_subsingleton.1 ((secEvalFun R U).map_isZero h0)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  first | (exact @GlobalTheory.EtC.resSec) | (exact GlobalTheory.EtC.resSec) | (intros; apply GlobalTheory.EtC.resSec  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def LieAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
    ∃ w : Fin D.a → (epsPtR x ⟶ A),
      (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
      v = (List.ofFn w).prod

def LieRankAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (g : R' →+* k) (i : Fin D.a),
    LieMult (act.toF D) (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m

def LieHer (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (R'' : Type) [CommRing R''] (g : R' →+* R''),
    LieAt b act (g.comp β) (spMap g ≫ x) ∧ LieRankAt b act (g.comp β) (spMap g ≫ x)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem TateIsoO.ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n m : ℕ) (x : D.La) :
    I.ev n (m • x) = I.ev n x ^ m := by
  let f : D.La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (I.ev n x)) fun x y => by
    simp [I.add]
  exact congrArg Additive.toMul (map_nsmul f m x)

theorem levelPos_of_coprime {N' : ℕ} (hc : N'.Coprime p) : 0 < N' := by
  rcases Nat.eq_zero_or_pos N' with h | h
  · subst h
    exact absurd ((Nat.coprime_zero_left p).1 hc) (Fact.out : p.Prime).one_lt.ne'
  · exact h

def Obj.forget {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) : Obj b N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta y := o.eta ((N' / N) • y)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_smul, Nat.div_mul_cancel hd, o.eta_ker]
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    have hN' := levelPos_of_coprime hc
    have hN : 0 < N := Nat.pos_of_dvd_of_pos hd hN'
    have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
    refine ⟨I, fun y => ?_⟩
    rw [hI, I.ev_nsmul]
    have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) y
    rwa [Nat.mul_div_cancel' hd] at this

@[simp] theorem Obj.forget_eta {b : Base D R} {N' : ℕ} {s : S ⟶ Sp R} (o : Obj b N' s) (N : ℕ) (hd : N ∣ N')
    (hc : N'.Coprime p) (y : D.La) : (o.forget N hd hc).eta y = o.eta ((N' / N) • y) := rfl

def IsLift {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (T : Over S)
    (lv : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧
  (∀ x, lv (N' • x) = 1) ∧
  (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
  (∀ x, lv ((N' / N) • x) = toUnit T ≫ o.eta x) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
    ∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OpenDim

theorem ringKrullDim_affineOpen (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη =
      Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul F Γ(Y, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(Y, U)).injective
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  exact ⟨d, h₁, (trdeg_eq_of_isAlgebraic_top F Γ(Y, U) Y.functionField).trans h₂⟩

theorem topologicalKrullDim_open (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra

  have chart : ∀ (V : Y.Opens) (x : Y), x ∈ V → ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V :=
    fun V x hx ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
      exact ⟨U, hU, hxU, hUV⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨U₀, hU₀, hx₀U₀, -⟩ := chart V x₀ hx₀
  obtain ⟨d₀, -, hd₀⟩ := ringKrullDim_affineOpen F f hU₀ ⟨x₀, hx₀U₀⟩
  have affDim : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = d₀ := fun U hU hUne ↦ by
    obtain ⟨d, h₁, h₂⟩ := ringKrullDim_affineOpen F f hU hUne
    obtain rfl : d = d₀ := by exact_mod_cast h₂.symm.trans hd₀
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have openDim : ∀ V : Y.Opens, (V : Set Y).Nonempty → topologicalKrullDim (V : Set Y) = d₀ :=
    fun V hV ↦ topologicalKrullDim_eq_of_forall_exists_isOpen hV fun x hx ↦ by
      obtain ⟨U, hU, hxU, hUV⟩ := chart V x hx
      refine ⟨U, U.isOpen, hxU, ?_⟩
      rw [Set.inter_eq_left.mpr hUV]
      exact affDim U hU ⟨x, hxU⟩
  have htop := openDim ⊤ ⟨x₀, trivial⟩
  rw [openDim V ⟨x₀, hx₀⟩, ← htop]
  exact (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Z := ((⊤ : Y.Opens) : Set Y)) (by simp))

theorem topologicalKrullDim_eq_of_isIso_restrict : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  intro F _ W W' _ _ p q h hp hq _ U hU hiso
  have hsurj : Function.Surjective (h ∣_ U) := (h ∣_ U).surjective
  have e₁ : topologicalKrullDim (U : Set W) = topologicalKrullDim (h ⁻¹ᵁ U) := by
    refine topologicalKrullDim_eq_of_isEmbedding ((h ∣_ U) ≫ U.ι).isOpenEmbedding.isEmbedding ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
  have e₂ : topologicalKrullDim ((h ⁻¹ᵁ U : W'.Opens) : Set W') =
      topologicalKrullDim (h ⁻¹ᵁ U) :=
    topologicalKrullDim_eq_of_isEmbedding (h ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding
      (Scheme.Opens.range_ι _)
  have hne : ((h ⁻¹ᵁ U : W'.Opens) : Set W').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨y, -⟩ := hsurj ⟨u, hu⟩
    exact ⟨(h ⁻¹ᵁ U).ι y, by rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩⟩
  rw [← topologicalKrullDim_open F q (h ⁻¹ᵁ U) hne, ← topologicalKrullDim_open F p U hU, e₁, e₂]

end GlobalTheory.OpenDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tw_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := fun q i =>
  GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits q i)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := by
  first | (exact @GlobalTheory.EtC.tw_finitary) | (exact GlobalTheory.EtC.tw_finitary) | (intros; apply GlobalTheory.EtC.tw_finitary  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace CupPull

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this
  exact this.symm

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cochain ((chains R).obj E') I n} {β : Cochain ((chains R).obj E') J m}
    {γ : Cochain ((chains R).obj E') K k} (h : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w hw U x
  rw [CupSpec.ev_pull, h N w hw U (x.map f)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]

end CupPull

theorem Pair.cup_pull : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  intro R _ I J K μ E E' f n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := Pair.aw_exists μ E' hk α β
  rw [Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]
  refine (Pair.cup_spec μ E hk _ _ _ ?_).symm
  have e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f) :=
    Cocycle.ofHom_coe _
  simp only [zcomp, Cocycle.mk_coe, e]
  exact CupPull.isAW_pull μ f hk hγ

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_hypercohomologyPullback : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) = μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  first | (exact @GlobalTheory.EtC.Pair.cup_pull) | (exact GlobalTheory.EtC.Pair.cup_pull) | (intros; apply GlobalTheory.EtC.Pair.cup_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAW
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem Pair.cup_spec_full : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  fun _ _ _ _ _ μ E _ _ _ hk => ⟨fun α β => μ.aw_exists E hk α β, fun α β γ h => μ.cup_spec E hk α β γ h⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_eq_class_of_isAW : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.EtC.Pair.cup_spec_full) | (exact GlobalTheory.EtC.Pair.cup_spec_full) | (intros; apply GlobalTheory.EtC.Pair.cup_spec_full  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZero
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem functionFieldPlaceOrder_inv {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (hx : x ≠ 0) :
    ord v x⁻¹ = - ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ord
  rw [map_inv₀, WithZero.log_inv, neg_neg]

theorem adjoin_simple_inv_eq (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

theorem finite_support_and_sum_ord_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  intro k F _ _ _ _ _ hF x hx
  by_cases htr : Transcendental k x
  · have htr' : Transcendental k x⁻¹ := by
      intro h
      apply htr
      have := h.inv
      rwa [inv_inv] at this
    obtain ⟨hA, hsA⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x htr
    obtain ⟨hB, hsB⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x⁻¹ htr'
    rw [adjoin_simple_inv_eq] at hsB
    set A := {v : Place k F | v.1 x < 1}
    set B := {v : Place k F | v.1 x⁻¹ < 1}
    have hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B := by
      intro v hv
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hv with h | h
      · exact Or.inl h
      · right
        show v.1 x⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
    refine ⟨(hA.union hB).subset hsub, ?_⟩
    have hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v := by
      intro v
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_trichotomy (v.1 x) 1 with h | h | h
      · have hB' : v ∉ B := by
          show ¬ v.1 x⁻¹ < 1
          rw [map_inv₀, not_lt]
          exact (one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le
        rw [Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]
      · have e : ord v x = 0 := by unfold ord; rw [h, WithZero.log_one, neg_zero]
        rw [e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'),
          Set.indicator_of_notMem (show v ∉ B from by
            show ¬ v.1 x⁻¹ < 1
            rw [map_inv₀, h, inv_one]; exact lt_irrefl _)]
        simp
      · have hA' : v ∉ A := fun h' => lt_asymm h h'
        have hB' : v ∈ B := by
          show v.1 x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h
        rw [Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]
    have hfA : (Function.support (A.indicator fun w => ord w x)).Finite :=
      hA.subset (Set.support_indicator_subset)
    have hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite :=
      hB.subset (Set.support_indicator_subset)
    rw [finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]
  · have halg : IsAlgebraic k x := by
      by_contra h
      exact htr h
    have hint : IsIntegral k x := halg.isIntegral
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k x hdeg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1 := fun v => v.2.2 c hc
    refine ⟨by simp [hv], ?_⟩
    have : ∀ v : Place k F, ord v (algebraMap k F c) = 0 := by
      intro v; unfold ord; rw [hv v, WithZero.log_one, neg_zero]
    simp [this]

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionField_finite_support_sum_order_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  first | exact @GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | exact GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | (intros; apply GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_hypercohomology_bijective : GlobalTheory.EtC.A1 := by
  first | (exact @GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (exact GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (intros; apply GlobalTheory.EtC.quasiIso_hypercohomology_bijective'  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ExtHom

variable {R : Type} [CommRing R]

theorem cochain_sgl_neg_one_eq_zero (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0]
    (β : Cochain (sgl F) I (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : p = 0
  · subst hp
    exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).eq_of_src _ _

theorem ofHom_eq_of_cls {T I : Cx R} {f g : T ⟶ I}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) :
    ∃ β : Cochain T I (-1), Cochain.ofHom f = δ (-1) 0 β + Cochain.ofHom g := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  rw [hβ]
  simp

end GlobalTheory.EtC.ExtHom


open GlobalTheory.EtC.ExtHom in
theorem GlobalTheory.EtC.extHom_of_quasiIso : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  intro R _ F T I _ _ ε _
  have hb := GlobalTheory.EtC.cpull_bijective_of_quasiIso R ε I 0
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨y, hy⟩ := hb.2 (CohomologyClass.mk (Cocycle.ofHom a))
    obtain ⟨z, rfl⟩ := y.mk_surjective
    refine ⟨Cocycle.homOf z, ?_⟩
    have hz : Cocycle.ofHom (ε ≫ Cocycle.homOf z) = zcomp (Cocycle.ofHom ε) z (zero_add 0) := by
      apply Cocycle.ext
      simp [zcomp, Cochain.ofHom_comp]
    have h2 : CohomologyClass.mk (Cocycle.ofHom (ε ≫ Cocycle.homOf z)) = CohomologyClass.mk (Cocycle.ofHom a) := by
      rw [hz]; exact hy
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls h2
    rw [cochain_sgl_neg_one_eq_zero F I β, δ_zero, zero_add] at hβ
    exact (Cocycle.equivHom _ _).injective (Cocycle.ext hβ)
  · have h1 : cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m)) = cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m')) := by
      simp only [cpull, cpre_mk]
      congr 1
      apply Cocycle.ext
      change (Cochain.ofHom ε).comp (Cochain.ofHom m) (zero_add 0) = (Cochain.ofHom ε).comp (Cochain.ofHom m') (zero_add 0)
      rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp, h]
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls (hb.1 h1)
    exact ⟨(Cochain.equivHomotopy m m').symm ⟨β, hβ⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  first | (exact @GlobalTheory.EtC.extHom_of_quasiIso) | (exact GlobalTheory.EtC.extHom_of_quasiIso) | (intros; apply GlobalTheory.EtC.extHom_of_quasiIso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBiject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBiject
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.LevelCx

open GlobalTheory.ColFilt

theorem zcomp_coe {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) : (zcomp a b h).1 = a.1.comp b.1 h := rfl

theorem ofHom_coe {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (Cocycle.ofHom f).1 = Cochain.ofHom f := rfl

theorem main : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) →
    ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
    (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) →
    ∀ n, Function.Bijective (cpull g I n) := by
  intro R _ I _ _ K L _ _ g hg
  have hb1 : ∀ p n' m (h : 0 + n' = m), Function.Bijective
      (cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I n' m h) := by
    intro p n' m h
    obtain rfl : n' = m := by omega
    exact hg p n'
  let Φ : ∀ n, (∀ _ : Unit, Cochain L I (n - 0)) →+ Cochain K I n := fun n =>
    AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp (α ()) (by omega))
      (fun α β => Cochain.comp_add _ _ _ _)
  have hΦ0 : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)), Φ n α = (Cochain.ofHom g).comp (α ()) (by omega) := fun _ _ => rfl
  have hΦ : ∀ n (α : ∀ _ : Unit, Cochain L I (n - 0)) (t q : ℤ) (hq : t + n = q),
      (Φ n α).v t q hq = g.f t ≫ (α ()).v t q (by omega) := by
    intro n α t q hq
    rw [hΦ0, Cochain.comp_v _ _ _ t t q (add_zero t) (by omega), Cochain.ofHom_v]
  have key : ∀ n' n (h : 0 + n' = n), Function.Bijective (cpre (Cocycle.ofHom g) I n' n h) := by
    intro n' n h
    obtain rfl : n' = n - 0 := by omega
    have := bijective_of_columns (isColumns_terms L) (isColumns_terms K) (fun _ : Unit => I) I (fun _ => 0) Φ
      (fun n m hnm α => by
        rw [hΦ0, hΦ0, δ_comp (Cochain.ofHom g) (α ()) _ 1 (m - 0) m hnm (zero_add 1) (by omega),
          δ_ofHom, Cochain.zero_comp, smul_zero, add_zero])
      (fun p n α hα => by
        show ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c → ιTerm K c k t h ≫ (Φ n α).v t q hq = 0
        intro c k t h q hq hc
        by_cases hk : k = 0
        · subst hk
          obtain rfl : c = t := by omega
          have h0 := eq_zero_of_ιTerm (hα () c 0 c h q (by omega) hc)
          rw [hΦ, h0, comp_zero, comp_zero]
        · rw [ιTerm_ne _ _ _ _ _ hk, zero_comp])
      (fun p _ => ⟨fun m x => cpre (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p))) I (m - 0) m
          (by omega) (x ()),
        fun m => (hb1 p (m - 0) m (by omega)).comp (Equiv.funUnique Unit _).bijective,
        fun n m h α _ a b ha hb => by
          refine congrArg CohomologyClass.mk (Cocycle.ext (Cochain.ext _ _ fun k q hq => ?_))
          rw [zcomp_coe, ofHom_coe, Cochain.comp_v _ _ _ k k q (add_zero k) (by omega), Cochain.ofHom_v, ha (), hb]
          by_cases hk : k = 0
          · subst hk
            rw [restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega), restr_v _ _ p _ _ _ _ 0 p q (add_zero p) _ (by omega),
              hΦ, ιTerm_zero, ιTerm_zero,
              show ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)).f 0 =
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ g.f p ≫
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.X p)).inv from
                HomologicalComplex.single_map_f_self _ _ _]
            exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))))
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) k hk).eq_of_src _ _⟩)
      n (fun x => cpre (Cocycle.ofHom g) I (n - 0) n h (x ()))
      (fun a b hb => congrArg CohomologyClass.mk (Cocycle.ext (by rw [zcomp_coe, hb]; rfl)))
    exact this.comp (Equiv.funUnique Unit _).symm.bijective
  intro n
  exact key n n (zero_add n)

end GlobalTheory.LevelCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBijectStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L), (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) → ∀ n, Function.Bijective (cpull g I n) := by
  first | (exact @GlobalTheory.LevelCx.main) | (exact GlobalTheory.LevelCx.main) | (intros; apply GlobalTheory.LevelCx.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LevelCmp

variable {R : Type} [CommRing R]

theorem cpull_comp_fun {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (I : Cx R) (n : ℤ) :
    ⇑(cpull (a ≫ b) I n) = ⇑(cpull a I n) ∘ ⇑(cpull b I n) :=
  funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x

theorem cpull_bij_of_heq {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  obtain ⟨hid, -, -, -, hhom⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have h1 := (hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1
  have h2 := (hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1
  have l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y := fun y => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]; exact (hid _ _ _ _).1
  have l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x := fun x => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]; exact (hid _ _ _ _).1
  exact ⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩

theorem cpull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull f I n) :=
  cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n

end GlobalTheory.EtC.LevelCmp


open GlobalTheory.EtC.LevelCmp in
theorem GlobalTheory.EtC.levelwise_eqv : GlobalTheory.EtC.A3 := by
  intro R _ E E' f F hlev
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI := hle E; haveI := hle E'; haveI := hge
  intro n
  refine GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n
  intro p k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨(-p).toNat, by omega⟩
    set φ := f.app (op (SimplexCategory.mk m))

    have hfree : Function.Bijective
        (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k) := by
      have hc := congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)
      simp only [cpull_comp_fun] at hc
      have hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘
          ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k)) :=
        (cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)
      rw [hc] at hr
      exact (Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr
    have hg : ((chains R).map f).f (-(m : ℤ)) =
        (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv := by
      rw [← Category.assoc, ← hnat f m]; simp
    rw [hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]
    exact (cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))
  · have h1 : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    have h2 : IsZero (((chains R).obj E').X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
    exact cpull_bij_of_iso _ _ k
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have hmap : liftSemi (toBaseChange R R' A).cot = E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
    simp only [liftSemi_tmul, LinearEquiv.coe_coe, E, LinearEquiv.trans_apply,
      AugCot.baseChangeEquiv_tmul_d, map_smul, AugCot.congr_d]
    exact congrArg (r • ·) ((toBaseChange R R' A).cot_d a)
  rw [hmap]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have hcomp : ((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega) =
      (liftSemi (toBaseChange R R' (G.A 1)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end PDivGroup

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZeroStatement
open GlobalTheory.PDiv

theorem GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero {p : ℕ} {R : Type}
    [CommRing R] (G : GlobalTheory.PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R']
    (hp : (p : R) = 0) : Function.Bijective (liftSemi (G.toBase R').omega) :=
  G.omega_baseChange_bijective R' hp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem glue_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T s hs
  have key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂) := by
    intro t₁ t₂ u₁ u₂ S w₁ w₂
    obtain ⟨n, b, hb, hb'⟩ := hdir t₁ t₂ S w₁ w₂
    refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)
    obtain ⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩ := hb' i S' u' hi
    have e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]
    have e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]
    have e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov T
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t, v, w, -⟩ := hb' i S u hi
      exact ⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t, v, w, e⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩
    rw [← e, ← e', ← mp_comp]
    exact key _ _ _ _ _ _ _
  refine ⟨x, fun t u ↦ ?_⟩
  have hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]

end GlobalTheory.CatCoh.Desc
end

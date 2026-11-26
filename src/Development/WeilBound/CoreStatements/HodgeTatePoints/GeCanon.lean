module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLine
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GeEmbSub
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

section alg

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]


open Classical in
noncomputable def ind (H : Subgroup T) : T → R := fun x => if x ∈ H then 1 else 0


open Classical in
noncomputable def extZero (H : Subgroup T) (a : H → R) : T → R := fun x => if h : x ∈ H then a ⟨x, h⟩ else 0

theorem ind_translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) (c : T) :
    (fun x => ind (R := R) H (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : c * t ∈ H
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 1 := by
      funext x
      have : c * (t * x) ∈ H := by
        rw [← _root_.mul_assoc]
        exact H.mul_mem h x.2
      simp [ind, this]
    rw [this]
    exact A.one_mem
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 0 := by
      funext x
      have : c * (t * x) ∉ H := by
        rw [← _root_.mul_assoc]
        exact fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [ind, this]
    rw [this]
    exact A.zero_mem

theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A)
    (hA : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A) {a : H → R} (ha : a ∈ A) : extZero H a ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : t ∈ H
  · have : (fun x : H => extZero H a (t * x)) = fun x => a (⟨t, h⟩ * x) := by
      funext x
      have h' : t * x ∈ H := H.mul_mem h x.2
      simp only [extZero, dif_pos h']
      rfl
    rw [this]
    exact hA a ha _
  · have : (fun x : H => extZero H a (t * x)) = 0 := by
      funext x
      have h' : t * x ∉ H := fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [extZero, h']
    rw [this]
    exact A.zero_mem

theorem translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) {f : T → R} (hf : f ∈ B) (c : T) :
    (fun x => f (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  simpa only [_root_.mul_assoc] using (hB f).1 hf (c * t)

def transl {B : Subalgebra R (T → R)} (hB : ∀ f ∈ B, ∀ c : T, (fun x => f (c * x)) ∈ B) (c : T) : B →+* B where
  toFun f := ⟨fun x => (f : T → R) (c * x), hB _ f.2 c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_translate_notMem [Finite T] {H : Subgroup T} {B : Subalgebra R (T → R)}
    (he : ∀ c : T, (fun x => ind (R := R) H (c * x)) ∈ B) (P : Ideal B) [P.IsPrime] :
    ∃ t : T, (⟨_, he t⁻¹⟩ : B) ∉ P := by
  classical
  have := Fintype.ofFinite T
  have h0 : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) = 0 := by
    apply Subtype.ext
    funext x
    have hx : ((∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B)) : B) : T → R) x
        = ∏ t : T, (1 - ind (R := R) H (t⁻¹ * x)) := by
      rw [← Subalgebra.coe_val, map_prod, Finset.prod_apply]
      rfl
    rw [hx]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [ind, H.one_mem])
  have hP : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) ∈ P := h0 ▸ P.zero_mem
  obtain ⟨t, -, ht⟩ := (Ideal.IsPrime.prod_mem_iff (p := P)).1 hP
  refine ⟨t, fun h => ?_⟩
  have : (1 : B) ∈ P := by
    have := P.add_mem ht h
    simpa using this
  exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›) this

end alg

section geom

theorem isAffineOpen_of_fin {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
    {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U) : IsAffineOpen U := by
  have := hF.finite
  have : IsAffineHom (U.ι ≫ Γ.G.hom) := inferInstance
  exact isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)

noncomputable def valRing {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valRing_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valRing x U h s = valAt x U h s := rfl

theorem spec_valRing_fromSpec {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (valRing x U h)) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : CommRingCat.ofHom (valRing x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := rfl
  rw [this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]
  simp

theorem fromSpec_mem' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (z) : hU.fromSpec z ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨z, rfl⟩

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem val_pullback (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (f : A) :
    valAt (Γ.pt t).left U h (ψ.hom f) = algebraMap R (FractionRing R) ((f : T → R) t) := by
  have e1 := spec_valRing_fromSpec (Γ.pt t).left hU h
  have e2 := hj.pt t
  rw [← e1, Category.assoc, ← hψ, ← Spec.map_comp] at e2
  have := congrArg (fun g => g.hom f) (Spec.map_injective e2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem val_mem_range [IsIntegrallyClosed R] (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U)
    (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (s : Γ(Γ.G.left, U)) :
    ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left U h s := _root_.GlobalTheory.CompanionTheory.Ar.BT.EmbSub.val_mem_range (U := U) (A := A) (j := j) Γ hF hU hj ψ hψ t h s

end geom

end PositivityTheory.HtPt.Ge.EmbSub

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

theorem openImmersion_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  intro R _ _ _ T _ _ Γ U hF j hj
  obtain ⟨H, A, hH, hA, hAs⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  have hTr : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := GlobalTheory.T.hopf_order_translation_invariant R H A hA
  have hOrder : Γ.btOrder U = Γ.btOrder ⊤ := by
    ext f
    rw [GlobalTheory.T.mem_btOrder_iff_btSet, GlobalTheory.T.mem_btOrder_iff_btSet]
    refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
    obtain ⟨R', _, _, _, _, hNormal, hFlat, hPrime⟩ :=
      @Htat.hens_normal R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
    have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
    obtain ⟨Γ', F, hBase⟩ :=
      PositivityTheory.UnitarySelfGeneration.bt_exists_bc R T Γ R' (algebraMap R R') hinj
    have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
      (IsFractionRing.injective R' (FractionRing R')).comp hinj
    let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
    have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) :=
      IsFractionRing.lift_algebraMap hinj'
    have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
    obtain ⟨g', hg, hClosed⟩ :=
      Scheme.exists_preimage_of_isPullback hBase.cart g (IsLocalRing.closedPoint R') (by
        apply PrimeSpectrum.ext
        exact hPrime.symm)
    have := Γ'.quasiFinite
    have := Γ'.finPres
    have := Γ'.separated
    have := Γ'.quasiCompact
    obtain ⟨U', hFinite, hClosedMem⟩ := Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
    have hSub := Twhopf.finite_sub R' T Γ' U' hFinite hClosedMem
    have hPullSub := GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hBase U hF
    have hle : F ⁻¹ᵁ U ≤ U' := Twhopf.finite_le R' _ Γ'.G.hom _ _ hPullSub.finite hClosedMem
    have hReg : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
      intro s x hx
      have := Htat.reg_pull R T Γ R' Γ' F hBase κ hκ _ x (hf s (F x) hx)
      simpa only [hκa] using this
    rw [← GlobalTheory.T.mem_btOrder_iff_btSet,
      ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hSub hPullSub hle,
      GlobalTheory.T.mem_btOrder_iff_btSet] at hReg
    rw [← hg]
    refine Htat.bt_reg_descent R T Γ R' Γ' F hBase hFlat κ hκ _ g' ?_
    simpa only [hκa] using hReg t g' (hClosedMem g' hClosed)
  have hB : ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h : H => f (t * h)) ∈ A := by
    intro f
    rw [← hOrder, GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAs _).2 ⟨s, fun x h => hs x h⟩
    · intro hf t
      obtain ⟨s, hs⟩ := (hAs _).1 (hf t)
      exact (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ⟨s, fun x h => hs ⟨x, (hH x).2 h⟩ h⟩
  let ψ : CommRingCat.of (Γ.btOrder ⊤) ⟶ Γ(Γ.G.left, U) := Spec.preimage (hU.fromSpec ≫ j)
  have hψ : Spec.map ψ = hU.fromSpec ≫ j := Spec.map_preimage _
  have hv := val_pullback Γ hU hj ψ hψ
  have hi := val_mem_range Γ hF hU hj ψ hψ
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hsurj : Function.Surjective ψ.hom := by
    intro s
    choose a ha using fun t : H => hi t ((hH t).1 t.2) s
    have haA : a ∈ A := (hAs a).2 ⟨s, fun t h => (ha t).symm⟩
    refine ⟨⟨extZero H a, extZero_mem hB hTr haA⟩, ?_⟩
    rw [← sub_eq_zero]
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
    have ht : t ∈ H := (hH t).2 h
    rw [← valRing_apply, map_sub, valRing_apply, valRing_apply, hv t h, ← ha ⟨t, ht⟩]
    simp [extZero, ht]
  have hz : ∀ f : Γ.btOrder ⊤, ψ.hom f = 0 ↔ ∀ t ∈ H, (f : T → R) t = 0 := by
    intro f
    constructor
    · intro hf t ht
      have := hv t ((hH t).1 ht) f
      rw [hf, ← valRing_apply, map_zero] at this
      exact inj (by rw [← this, map_zero])
    · intro hf
      refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
      rw [hv t h, hf t ((hH t).2 h), map_zero]
  let e : Γ.btOrder ⊤ := ⟨_, ind_translate_mem hB 1⟩
  have he1 : ∀ x ∈ H, (e : T → R) x = 1 := fun x hx => by simp [e, ind, hx]
  have he0 : ∀ x, x ∉ H → (e : T → R) x = 0 := fun x hx => by simp [e, ind, hx]
  have hidem : IsIdempotentElem e := by
    apply Subtype.ext
    funext x
    change (e : T → R) x * (e : T → R) x = (e : T → R) x
    by_cases hx : x ∈ H
    · simp [he1 x hx]
    · simp [he0 x hx]
  have hker : RingHom.ker ψ.hom = Ideal.span {1 - e} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton', hz]
    constructor
    · intro hf
      refine ⟨f, Subtype.ext (funext fun x => ?_)⟩
      change (f : T → R) x * (1 - (e : T → R) x) = (f : T → R) x
      by_cases hx : x ∈ H
      · simp [hf x hx]
      · simp [he0 x hx]
    · rintro ⟨b, rfl⟩ t ht
      change (b : T → R) t * (1 - (e : T → R) t) = 0
      simp [he1 t ht]
  have hoi : IsOpenImmersion (Spec.map ψ) :=
    (isOpenImmersion_SpecMap_iff_of_surjective ψ hsurj).2 ⟨1 - e, hidem.one_sub, hker⟩
  refine ⟨?_, ?_⟩
  · have : U.ι ≫ j = hU.isoSpec.hom ≫ Spec.map ψ := by
      rw [hψ, ← hU.isoSpec_inv_ι]
      simp
    rw [this]
    infer_instance
  · intro P
    have hBt : ∀ f ∈ Γ.btOrder ⊤, ∀ c : T, (fun x => f (c * x)) ∈ Γ.btOrder ⊤ :=
      fun f hf c => translate_mem hB hf c
    obtain ⟨t, ht⟩ := exists_translate_notMem (B := Γ.btOrder ⊤) (H := H) (ind_translate_mem hB) P.asIdeal
    let Q : Ideal (Γ.btOrder ⊤) := P.asIdeal.comap (transl hBt t⁻¹)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have heQ : e ∉ Q := by
      intro h
      apply ht
      have : transl hBt t⁻¹ e = ⟨_, ind_translate_mem hB t⁻¹⟩ :=
        Subtype.ext (funext fun x => by simp [transl, e])
      rw [← this]
      exact h
    have h1e : 1 - e ∈ Q := by
      have h0 : e * (1 - e) ∈ Q := by
        rw [mul_sub, _root_.mul_one, hidem.eq, sub_self]
        exact Q.zero_mem
      exact (hQ.mem_or_mem h0).resolve_left heQ
    have hk : RingHom.ker ψ.hom ≤ Q := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact h1e
    obtain ⟨Q', hQ'⟩ : (⟨Q, hQ⟩ : PrimeSpectrum (Γ.btOrder ⊤)) ∈ Set.range (PrimeSpectrum.comap ψ.hom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact hk
    refine ⟨t, hU.fromSpec Q', fromSpec_mem' hU _, fun f f' hff => ?_⟩
    have hjg : (j (hU.fromSpec Q')).asIdeal = Q := by
      have h1 : j (hU.fromSpec Q') = (Spec.map ψ) Q' := by
        rw [hψ]
        rfl
      rw [h1]
      exact congrArg PrimeSpectrum.asIdeal hQ'
    rw [hjg]
    have h2 : transl hBt t⁻¹ f' = f :=
      Subtype.ext (funext fun x => by
        change (f' : T → R) (t⁻¹ * x) = (f : T → R) x
        rw [hff, mul_inv_cancel_left])
    change f ∈ P.asIdeal ↔ transl hBt t⁻¹ f' ∈ P.asIdeal
    rw [h2]

end PositivityTheory.HtPt.Ge.EmbSub
end

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

theorem exists_der (ρ : B →ₐ[R] TrivSqZeroExt R V) (h : ∀ f, (ρ f).fst = ε f) :
    ∃ ψ : (RingHom.ker ε).Cotangent →ₗ[R] V, derRing ε ψ = ρ := by
  have hz : ∀ x ∈ (RingHom.ker ε) ^ 2, (ρ x).snd = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have h1 : (ρ a).fst = 0 := (h a).trans ha
      have h2 : (ρ b).fst = 0 := (h b).trans hb
      rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2]
      simp
    · intro a b ha hb
      rw [map_add (f := _), TrivSqZeroExt.snd_add, ha, hb, add_zero]
  let d : RingHom.ker ε →ₗ[R] V :=
    { toFun := fun f => (ρ f.1).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  let tC : RingHom.ker ε →ₗ[R] (RingHom.ker ε).Cotangent :=
    { toFun := fun f => (RingHom.ker ε).toCotangent f
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => by
        have : r • a = (algebraMap R B r) • a := (algebraMap_smul B r a).symm
        rw [this, map_smul]
        exact algebraMap_smul B r _ }
  have hs : Function.Surjective tC := Ideal.toCotangent_surjective _
  have hk : LinearMap.ker tC ≤ LinearMap.ker d := by
    intro a ha
    exact hz _ ((Ideal.toCotangent_eq_zero _ _).1 ha)
  let ψ : (RingHom.ker ε).Cotangent →ₗ[R] V :=
    ((LinearMap.ker tC).liftQ d hk) ∘ₗ (tC.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hψ : ∀ a, ψ (tC a) = d a := by
    intro a
    have : (tC.quotKerEquivOfSurjective hs).symm (tC a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨ψ, AlgHom.ext fun f => ?_⟩
  rw [derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [h]
  · have : ψ ((RingHom.ker ε).toCotangent (augPart ε f)) = d (augPart ε f) := hψ _
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, this]
    change (ρ (f - algebraMap R B (ε f))).snd = _
    rw [map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem derRing_comp (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (π : V →ₗ[R] V') (f : B) :
    TrivSqZeroExt.map π (derRing ε ψ f) = derRing ε (π ∘ₗ ψ) f := by
  rw [derRing_apply, derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp
end Alg

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

theorem one_left_eq {B : Scheme.{0}} {X M : Over B} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

include Γ in
theorem unit_i (ht : Γ.IsTorsionAlong G x N i) (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let w : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    change ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, Over.w])
  have h := ht.mul Y 1 1 w w rfl rfl
  rw [_root_.mul_one] at h
  have h1 : w * w = w * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h
  have h2 : w = 1 := mul_left_cancel h1
  exact congrArg CommaMorphism.left h2

theorem unit_i' (ht : Γ.IsTorsionAlong G x N i) : η[Γ.G].left ≫ i = x ≫ η[G].left := by
  have h := unit_i Γ ht (Over.mk (𝟙 _))
  rw [one_left_eq, one_left_eq] at h
  simpa using h

theorem unit_j (hj : Γ.IsEmb (Γ.btOrder ⊤) j) :
    η[Γ.G].left ≫ j = Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  have h1 : (Γ.pt 1).left = (genPt R).hom ≫ η[Γ.G].left := by
    rw [map_one, one_left_eq]
  have h2 := hj.pt 1
  rw [h1, Category.assoc] at h2
  let ρ := Spec.preimage (η[Γ.G].left ≫ j)
  have hρ : Spec.map ρ = η[Γ.G].left ≫ j := Spec.map_preimage _
  rw [← hρ]
  rw [← hρ] at h2
  change Spec.map _ ≫ Spec.map ρ = _ at h2
  rw [← Spec.map_comp] at h2
  have h3 := Spec.map_injective h2
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  have h4 := congrArg (fun g => g.hom f) h3
  exact IsFractionRing.injective R (FractionRing R) h4

theorem zsec_surj : Function.Surjective (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom R R V).toRingHom)) := by
  intro p
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (TrivSqZeroExt R V)) p
  refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (TrivSqZeroExt R V) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  set b := algebraMap R (TrivSqZeroExt R V) a.fst with hb
  have h0 : (b - a).fst = 0 := by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : b - a ∈ p.asIdeal := by
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : (b - a) ^ 2 = 0 := by
      rw [pow_two]
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h0]
    rw [this]; exact zero_mem _
  constructor
  · intro h; simpa using p.asIdeal.sub_mem h hm
  · intro h; simpa using p.asIdeal.add_mem hm h

theorem spec_fst_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) =
    Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (congrArg TrivSqZeroExt.fst (derRing_apply (ev1 Γ) ψ f)).trans (by simp)

theorem spec_alg_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (derRing (ev1 Γ) ψ).commutes r

theorem rel_of_torsion (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (v : ob x V ⟶ G) (h1 : zsec x ≫ v = 1) (hN : v ^ N = 1) :
    ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, TanRel Γ i j ψ v := by
  obtain ⟨y', hy'⟩ := (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).1 hN
  let y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left := y'.left
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := Over.w y'
  have y3 : y ≫ i = v.left := hy'
  let ρ₀ := Spec.preimage (y ≫ j)
  have hρ : Spec.map ρ₀ = y ≫ j := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)) ≫ ρ₀ =
      CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, Category.assoc, hj.isOver, y1]
  let ρ : (Γ.btOrder ⊤) →ₐ[R] TrivSqZeroExt R V :=
    { ρ₀.hom with
      commutes' := fun r => congrArg (fun g => g.hom r) hc }
  let a := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have e1 : a ≫ y = η[Γ.G].left := by
    have := ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by
        change (a ≫ y) ≫ Γ.G.hom = 𝟙 _
        rw [Category.assoc, y1, ha])) 1 (by
      rw [one_left_eq]
      simp only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]
      rw [unit_i' Γ ht, y3]
      have := congrArg Over.Hom.left h1
      rw [one_left_eq, Over.comp_left] at this
      exact this)
    have h := congrArg Over.Hom.left this
    rw [one_left_eq] at h
    simpa using h
  have hfst : ∀ f, (ρ f).fst = ev1 Γ f := by
    have h2 : Spec.map (ρ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) =
        Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
      rw [Spec.map_comp, hρ, ← Category.assoc, e1, unit_j Γ hj]
    have h3 := Spec.map_injective h2
    intro f
    exact congrArg (fun g => g.hom f) h3
  obtain ⟨ψ, hψ⟩ := exists_der (ev1 Γ) ρ hfst
  refine ⟨ψ, y, y1, ?_, y3⟩
  rw [hψ, ← hρ]
  rfl

theorem rel_unique (ht : Γ.IsTorsionAlong G x N i) {ψ ψ' : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ' v) : ψ = ψ' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have e := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) (Over.homMk y a)
    (Over.homMk y' a') (by simpa using c.trans c'.symm)
  have e' : y = y' := congrArg CommaMorphism.left e
  rw [e', b'] at b
  have h3 := Spec.map_injective b
  apply derRing_injective (ev1 Γ)
  apply AlgHom.ext
  intro f
  exact (congrArg (fun g => g.hom f) h3).symm

theorem rel_map {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G} (h : TanRel Γ i j ψ v) (π : V →ₗ[R] V') :
    TanRel Γ i j (π ∘ₗ ψ) (hom x π ≫ v) := by
  obtain ⟨y, a, b, c⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map π).toRingHom) ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc, a, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (TrivSqZeroExt.map π).commutes r
  · rw [Category.assoc, b, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact derRing_comp (ev1 Γ) ψ π f
  · rw [Category.assoc, c]
    rfl

end Rel

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

theorem hom_add' {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
    [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  GlobalTheory.T.hom_add_mul_of_unit_section S R x G P V u hu f g

theorem val_of_emb {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)) (hs : Γ.HasValues s (f : T → R))
    {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B)
    (h : y ≫ j = Spec.map (CommRingCat.ofHom ρ)) : valAt y ⊤ le_top s = ρ f :=
  GlobalTheory.T.bt_order_value_eval R T Γ j hj f s hs B y ρ h

theorem dual_eq_smul {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Projective R L] (N : ℕ)
    (d : Module.Dual R L) (h : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) (d e) = 0) :
    ∃ u : Module.Dual R L, d = N • u := _root_.GlobalTheory.CompanionTheory.Ar.BT.Tan.dual_eq_smul (R := R) (L := L) N d h

end PositivityTheory.HtPt.Ge.Tan

namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

theorem hom_nsmul (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] (φ : P →ₗ[R] V) (n : ℕ) : hom x (n • φ) ≫ u = (hom x φ ≫ u) ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero, hom_zero, Category.assoc, hu, MonObj.comp_one]
  | succ n ih => rw [succ_nsmul, hom_add' x G u hu, ih, pow_succ]

theorem hom_zero_comp (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] : hom x (0 : P →ₗ[R] V) ≫ u = 1 := by
  rw [hom_zero, Category.assoc, hu, MonObj.comp_one]

end Core

end PositivityTheory.HtPt.Ge.Tan

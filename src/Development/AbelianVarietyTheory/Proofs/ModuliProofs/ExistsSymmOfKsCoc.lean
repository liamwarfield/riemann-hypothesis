module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstFnCompSpMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSymmOfSquare

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerOfIsPushout
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.ProdLift

def derHom {S B : Type} [CommRing S] [CommRing B] (a : S →+* B) (δ : S → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = a x * δ y + a y * δ x) :
    S →+* DualNumber B where
  toFun x := TrivSqZeroExt.inl (a x) + TrivSqZeroExt.inr (δ x)
  map_one' := by
    have h' := hmul 1 1
    rw [_root_.mul_one, map_one, _root_.one_mul] at h'
    have h : δ 1 = 0 := left_eq_add.mp h'
    ext <;> simp [h]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero, left_eq_add] at h
    ext <;> simp [h]
  map_add' x y := by ext <;> simp [hadd]
  map_mul' x y := by ext <;> simp [hmul, mul_comm]

theorem exists_der_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (δ : S → B) (δ' : T → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = a (u.hom x) * δ y + a (u.hom y) * δ x)
    (hadd' : ∀ x y, δ' (x + y) = δ' x + δ' y)
    (hmul' : ∀ x y, δ' (x * y) = a (v.hom x) * δ' y + a (v.hom y) * δ' x)
    (hR : ∀ r, δ (i.hom r) = δ' (j.hom r)) :
    ∃ d : P → B, (∀ x y, d (x + y) = d x + d y) ∧ (∀ x y, d (x * y) = a x * d y + a y * d x) ∧
      (∀ x, d (u.hom x) = δ x) ∧ ∀ x, d (v.hom x) = δ' x := by
  let φ₁ : S →+* DualNumber B := derHom (a.comp u.hom) δ hadd hmul
  let φ₂ : T →+* DualNumber B := derHom (a.comp v.hom) δ' hadd' hmul'
  have hw : i ≫ CommRingCat.ofHom φ₁ = j ≫ CommRingCat.ofHom φ₂ := by
    ext r
    have e : u.hom (i.hom r) = v.hom (j.hom r) := by
      rw [← CommRingCat.comp_apply, po.w, CommRingCat.comp_apply]
    · simp [φ₁, φ₂, derHom, e]
    · simp [φ₁, φ₂, derHom, hR]
  let Φ := po.desc (CommRingCat.ofHom φ₁) (CommRingCat.ofHom φ₂) hw
  have hΦu : ∀ x, Φ.hom (u.hom x) = φ₁ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inl_desc]
    rfl
  have hΦv : ∀ x, Φ.hom (v.hom x) = φ₂ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inr_desc]
    rfl
  have hfst : Φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom = CommRingCat.ofHom a := by
    apply po.hom_ext
    · ext x
      simp [hΦu, φ₁, derHom]
    · ext x
      simp [hΦv, φ₂, derHom]
  have hf : ∀ x, (Φ.hom x).fst = a x := fun x => by
    have := congrArg (fun g => g.hom x) hfst
    simpa using this
  refine ⟨fun x => (Φ.hom x).snd, fun x y => ?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · simp
  · simp only [map_mul, TrivSqZeroExt.snd_mul, hf, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring
  · simp [hΦu, φ₁, derHom]
  · simp [hΦv, φ₂, derHom]

theorem der_eq_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (d d' : P → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = a x * d y + a y * d x)
    (hadd' : ∀ x y, d' (x + y) = d' x + d' y)
    (hmul' : ∀ x y, d' (x * y) = a x * d' y + a y * d' x)
    (hu : ∀ x, d (u.hom x) = d' (u.hom x)) (hv : ∀ x, d (v.hom x) = d' (v.hom x)) : d = d' := by
  have hext : u ≫ CommRingCat.ofHom (derHom a d hadd hmul) = u ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') ∧
      v ≫ CommRingCat.ofHom (derHom a d hadd hmul) = v ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') := by
    constructor
    · ext x
      · simp [derHom]
      · simp [derHom, hu]
    · ext x
      · simp [derHom]
      · simp [derHom, hv]
  have hφ := po.hom_ext hext.1 hext.2
  funext x
  have := congrArg (fun g => (g.hom x).snd) hφ
  simpa [derHom] using this

theorem pbT_eq {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  rw [dite_eq_left h]

theorem appLE_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R)
    (f : Y ⟶ X) (hf : f ≫ q = q') {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  unfold constFn
  have e := Scheme.Hom.appLE_comp_appLE f q ⊤ U V (by simp) h
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

theorem app_appLE {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W)
    (h' : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W) (f : Γ(X, W)) :
    (m₂.app Q).hom ((p.appLE W Q h).hom f) = (p₀.appLE _ _ h').hom ((m.app W).hom f) := by
  have key : ∀ (g g' : Z₀ ⟶ X) (e : g = g') (h₁ : m₂ ⁻¹ᵁ Q ≤ g ⁻¹ᵁ W) (h₂ : m₂ ⁻¹ᵁ Q ≤ g' ⁻¹ᵁ W),
      (g.appLE W (m₂ ⁻¹ᵁ Q) h₁).hom f = (g'.appLE W (m₂ ⁻¹ᵁ Q) h₂).hom f := by
    rintro g _ rfl _ _
    rfl
  have e₁ := Scheme.Hom.appLE_comp_appLE m₂ p W Q (m₂ ⁻¹ᵁ Q) h le_rfl
  have e₂ := Scheme.Hom.appLE_comp_appLE p₀ m W (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) le_rfl h'
  rw [Scheme.Hom.app_eq_appLE m₂, Scheme.Hom.app_eq_appLE m]
  have l₁ := congrArg (fun g => g.hom f) e₁
  have l₂ := congrArg (fun g => g.hom f) e₂
  simp only [CommRingCat.comp_apply] at l₁ l₂
  rw [l₁, l₂]
  exact key _ _ hp _ _

theorem preimage_le {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W) :
    m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := by
  intro x hx
  have h₁ : p (m₂ x) ∈ W := h hx
  change m (p₀ x) ∈ W
  rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
  exact h₁

theorem finiteRing_sq_sub_mul_sq_eq_of_card {K : Type} [Field K] {R : Type} [CommRing R] {Z Z₀ X Y : Scheme.{0}}
    {p q : Z ⟶ X} {s : X ⟶ Sp R} (H : IsPullback p q s s) {z : Z ⟶ Sp R} (hz : p ≫ s = z)
    {p₀ q₀ : Z₀ ⟶ Y} {s₀ : Y ⟶ Sp K} {z₀ : Z₀ ⟶ Sp K} (hp₀ : p₀ ≫ s₀ = z₀) (hq₀ : q₀ ≫ s₀ = z₀)
    {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z} (hp : m₂ ≫ p = p₀ ≫ m) (hq : m₂ ≫ q = q₀ ≫ m) (D : R → K)
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (Q : Z.Opens)
    (hQ : Q = p ⁻¹ᵁ W ⊓ q ⁻¹ᵁ W') :
    (∀ d d', LocDerK s₀ s m D W d → LocDerK s₀ s m D W' d' → ∃ d₂, LocDerK z₀ z m₂ D Q d₂ ∧
      (∀ f, d₂ Q (pbT p f Q) = pbT p₀ (d W f) _) ∧ ∀ f, d₂ Q (pbT q f Q) = pbT q₀ (d' W' f) _) ∧
    ∀ d₂ d₂', LocDerK z₀ z m₂ D Q d₂ → LocDerK z₀ z m₂ D Q d₂' →
      (∀ f : Γ(X, W), d₂ Q (pbT p f Q) = d₂' Q (pbT p f Q)) →
      (∀ f : Γ(X, W'), d₂ Q (pbT q f Q) = d₂' Q (pbT q f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  have hWQ : Q ≤ p ⁻¹ᵁ W := by rw [hQ]; exact inf_le_left
  have hW'Q : Q ≤ q ⁻¹ᵁ W' := by rw [hQ]; exact inf_le_right
  have h₁ : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := preimage_le hp hWQ
  have h₂ : m₂ ⁻¹ᵁ Q ≤ q₀ ⁻¹ᵁ m ⁻¹ᵁ W' := preimage_le hq hW'Q
  have hz' : q ≫ s = z := H.w.symm.trans hz
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have : IsAffine (⊤ : (Sp R).Opens).toScheme := isAffineOpen_top (Sp R)
  have hPb := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W') (UX := W) (by simp) (by simp) hQ
  have : IsAffine Q.toScheme := IsAffine.of_isPullback hPb
  have hQa : IsAffineOpen Q := this
  have hPo : IsPushout (s.appLE ⊤ W (by simp)) (s.appLE ⊤ W' (by simp)) (p.appLE W Q hWQ)
      (q.appLE W' Q hW'Q) :=
    (isPushout_appTop_of_isPullback hPb).of_iso (Scheme.Opens.topIso ⊤) W.topIso W'.topIso Q.topIso
      (Arrow.w (arrowResLEAppIso s ⊤ W _).hom).symm (Arrow.w (arrowResLEAppIso s ⊤ W' _).hom).symm
      (Arrow.w (arrowResLEAppIso p W Q _).hom).symm (Arrow.w (arrowResLEAppIso q W' Q _).hom).symm
  refine ⟨fun d d' hd hd' => ?_, fun d₂ d₂' e₁ e₂ ef ef' O hO => ?_⟩
  · let δ : Γ(X, W) → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (p₀.appLE (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) h₁).hom (d W f)
    let δ' : Γ(X, W') → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (q₀.appLE (m ⁻¹ᵁ W') (m₂ ⁻¹ᵁ Q) h₂).hom (d' W' f)
    have hb : ∀ r, δ (constFn s W r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ]
      rw [hd.base W le_rfl r]
      exact appLE_constFn s₀ z₀ p₀ hp₀ h₁ (D r)
    have hb' : ∀ r, δ' (constFn s W' r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ']
      rw [hd'.base W' le_rfl r]
      exact appLE_constFn s₀ z₀ q₀ hq₀ h₂ (D r)
    have hR : ∀ r, δ ((s.appLE ⊤ W (by simp)).hom r) = δ' ((s.appLE ⊤ W' (by simp)).hom r) := by
      intro r
      obtain ⟨r', rfl⟩ : ∃ r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r' = r :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, by simp⟩
      change δ (constFn s W r') = δ' (constFn s W' r')
      rw [hb, hb']
    obtain ⟨d0, hadd0, hmul0, hu0, hv0⟩ := exists_der_of_isPushout hPo (m₂.app Q).hom δ δ'
      (fun x y => by simp only [δ]; rw [hd.add W le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ]
        rw [hd.mul W le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hp hWQ h₁ x, app_appLE hp hWQ h₁ y])
      (fun x y => by simp only [δ']; rw [hd'.add W' le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ']
        rw [hd'.mul W' le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hq hW'Q h₂ x, app_appLE hq hW'Q h₂ y])
      hR
    have hbQ : ∀ r, d0 (constFn z Q r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      rw [← appLE_constFn s z p hz hWQ r, hu0, hb]
    obtain ⟨d₂, hd₂, hd₂Q⟩ := GlobalTheory.LocDerExtK.exists_locDerK K R Z₀ Z z₀ z m₂ D Q hQa d0 hadd0 hmul0 hbQ
    refine ⟨d₂, hd₂, fun f => ?_, fun f => ?_⟩
    · rw [hd₂Q, pbT_eq p f hWQ, hu0, pbT_eq p₀ _ h₁]
    · rw [hd₂Q, pbT_eq q f hW'Q, hv0, pbT_eq q₀ _ h₂]
  · refine GlobalTheory.LocDerExtK.locDerK_unique hQa d₂ d₂' e₁ e₂ ?_ O hO
    exact der_eq_of_isPushout hPo (m₂.app Q).hom (d₂ Q) (d₂' Q) (e₁.add Q le_rfl) (e₁.mul Q le_rfl)
      (e₂.add Q le_rfl) (e₂.mul Q le_rfl)
      (fun x => by rw [← pbT_eq p x hWQ]; exact ef x) (fun x => by rw [← pbT_eq q x hW'Q]; exact ef' x)

theorem main : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (A : Over (Sp R)) (A₀ : Over (Sp K)) (m : A₀.left ⟶ A.left) (m₂ : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left) (D : R → K) (W W' : A.left.Opens), m ≫ A.hom = A₀.hom ≫ spMap x₀ → IsSquare m m₂ → IsAffineOpen W → IsAffineOpen W' → ∀ Q, Q = (fst A A).left ⁻¹ᵁ W ⊓ (snd A A).left ⁻¹ᵁ W' → (∀ d d', LocDerK A₀.hom A.hom m D W d → LocDerK A₀.hom A.hom m D W' d' → ∃ d₂, LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ ∧ (∀ f, d₂ Q (pbT (fst A A).left f Q) = pbT (fst A₀ A₀).left (d W f) _) ∧ ∀ f, d₂ Q (pbT (snd A A).left f Q) = pbT (snd A₀ A₀).left (d' W' f) _) ∧ ∀ d₂ d₂', LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ → LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂' → (∀ f : Γ(A.left, W), d₂ Q (pbT (fst A A).left f Q) = d₂' Q (pbT (fst A A).left f Q)) → (∀ f : Γ(A.left, W'), d₂ Q (pbT (snd A A).left f Q) = d₂' Q (pbT (snd A A).left f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  intro K _ R _ x₀ A A₀ m m₂ D W W' _ hsq hW hW' Q hQ
  obtain ⟨hs₁, hs₂⟩ := hsq
  exact finiteRing_sq_sub_mul_sq_eq_of_card (Over.isPullback_of_binaryFan_isLimit _
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A A))
    (Over.w (fst A A)) (Over.w (fst A₀ A₀)) (Over.w (snd A₀ A₀)) hs₁ hs₂ D hW hW' Q hQ

end GlobalTheory.KS.ProdLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLieCombZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.SquareField
variable {K : Type} [Field K]

def zeroPt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isTangent_iff {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsTangent v ↔ zeroPt K ≫ v = η[G] := by
  unfold IsTangent
  constructor
  · intro h
    ext1
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun u => u.left) h

theorem isTangent_one {G : Over (Sp K)} [GrpObj G] : IsTangent (1 : epsR K ⟶ G) := by
  rw [isTangent_iff, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt K ≫ toUnit _) (𝟙 _),
    Category.id_comp]

theorem isTangent_lift {G H : Over (Sp K)} [GrpObj G] [GrpObj H] {v : epsR K ⟶ G} {w : epsR K ⟶ H}
    (hv : IsTangent v) (hw : IsTangent w) : IsTangent (lift v w) := by
  rw [isTangent_iff] at hv hw ⊢
  apply CartesianMonoidalCategory.hom_ext
  · simp [hv]
  · simp [hw]

theorem isLieComb_one {G : Over (Sp K)} [GrpObj G] (v : epsR K ⟶ G) :
    IsLieComb (fun _ : Fin 1 => (1 : K)) (fun _ => v) v := by
  refine ⟨fun _ => v, fun _ => ?_, by simp⟩
  simp only [epsScaleR, one_smul, TrivSqZeroExt.map_id]
  simp [spMap]

theorem isLieComb_zero {G : Over (Sp K)} [GrpObj G] :
    IsLieComb (fun _ : Fin 0 => (1 : K)) (fun _ => (1 : epsR K ⟶ G)) 1 := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem app_eq_pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (h : Γ(Y, W)) :
    (f.app W).hom h = pbT f h (f ⁻¹ᵁ W) := by
  unfold pbT
  rw [dite_eq_left le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_one {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) : constFn q O 1 = 1 := by
  simp [constFn]

private theorem pbT_eq_rsT_pbT_preimage {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀))
    (O : Z.Opens) (hO : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = rsT (pbT f s (f ⁻¹ᵁ O₀)) O := by
  unfold pbT rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left (le_refl _), resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem rsT_zero_moduli {Y : Scheme.{0}} {O₀ : Y.Opens} (O : Y.Opens) :
    rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT
  split <;> simp

section
variable {A₁ A₀ : Over (Sp K)} [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) [IsMonHom f]
  {w : epsR K ⟶ A₁} {dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)}

theorem field_pb {v : epsR K ⟶ A₀} {dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)}
    (hv : IsTangent v) (hd : IsInvDer v dd) (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = v)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = pbT f.left (dd W h) O := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 1 (fun _ => v) (fun _ => dd) w dw (fun _ => 1) inferInstance
    (fun _ => hv) hw (fun _ => hd) hdw (by rw [e]; exact isLieComb_one v) W h
  simp only [Fin.sum_univ_one, constFn_one] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, _root_.one_mul, app_eq_pbT,
    ← pbT_eq_rsT_pbT_preimage f.left (dd W h) O hO]

theorem field_pb_zero (hw : IsTangent w) (hdw : IsInvDer w dw) (e : w ≫ f = 1)
    (W : A₀.left.Opens) (h : Γ(A₀.left, W)) (O : A₁.left.Opens) (hO : O ≤ f.left ⁻¹ᵁ W) :
    dw O (pbT f.left h O) = 0 := by
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₁ w hw
  obtain ⟨-, -, hres, -, -⟩ := hprop dw hdw
  have hkey := GlobalTheory.T.invariantVectorFields_along_groupHom K A₁ A₀ f 0 (fun _ => 1) (fun _ _ x => x) w dw (fun _ => 1) inferInstance
    (fun i => i.elim0) hw (fun i => i.elim0) hdw (by rw [e]; exact isLieComb_zero) W h
  simp only [Fin.sum_univ_zero] at hkey
  rw [pbT_eq_rsT_pbT_preimage f.left h O hO, hres _ _ _ hO, ← app_eq_pbT, hkey, rsT_zero_moduli]
end

theorem main : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), IsTangent v → IsInvDer v dd → ∀ (n n' : A₀ ⊗ A₀ ⟶ A₀), ((n = fst A₀ A₀ ∧ n' = snd A₀ A₀) ∨ (n = snd A₀ A₀ ∧ n' = fst A₀ A₀)) → ∃ dw : ∀ O : (A₀ ⊗ A₀).left.Opens, Γ((A₀ ⊗ A₀).left, O) → Γ((A₀ ⊗ A₀).left, O), (∀ W f f', dw W (f + f') = dw W f + dw W f') ∧ (∀ W f f', dw W (f * f') = f * dw W f' + f' * dw W f) ∧ (∀ W W' (f : Γ((A₀ ⊗ A₀).left, W)), W' ≤ W → dw W' (rsT f W') = rsT (dw W f) W') ∧ (∀ W a, dw W (constFn (A₀ ⊗ A₀).hom W a) = 0) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ (fst A₀ A₀ * snd A₀ A₀).left ⁻¹ᵁ W → dw O (pbT (fst A₀ A₀ * snd A₀ A₀).left h O) = pbT (fst A₀ A₀ * snd A₀ A₀).left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n.left ⁻¹ᵁ W → dw O (pbT n.left h O) = pbT n.left (dd W h) O) ∧ (∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)) O, O ≤ n'.left ⁻¹ᵁ W → dw O (pbT n'.left h O) = 0) := by
  intro K _ A₀ _ _ v dd hv hd n n' hnn'
  obtain ⟨w, hw, hwn, hwn', hwm⟩ : ∃ w : epsR K ⟶ A₀ ⊗ A₀, IsTangent w ∧ w ≫ n = v ∧ w ≫ n' = 1 ∧
      w ≫ (fst A₀ A₀ * snd A₀ A₀) = v := by
    rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨lift v 1, isTangent_lift hv isTangent_one, lift_fst _ _, lift_snd _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.mul_one]⟩
    · exact ⟨lift 1 v, isTangent_lift isTangent_one hv, lift_snd _ _, lift_fst _ _, by
        rw [MonObj.comp_mul, lift_fst, lift_snd, _root_.one_mul]⟩
  have hn : IsMonHom n := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hn' : IsMonHom n' := by rcases hnn' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> infer_instance
  have hm : IsMonHom (fst A₀ A₀ * snd A₀ A₀) := by
    rw [← MonObj.mul_eq_mul]
    infer_instance
  obtain ⟨-, hprop⟩ := GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K (A₀ ⊗ A₀) w hw).1
  obtain ⟨hadd, hmul, hres, hconst, -⟩ := hprop dw hdw
  refine ⟨dw, hadd, hmul, hres, hconst, ?_, ?_, ?_⟩
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwm W h O hO
  · intro W h O hO
    exact field_pb _ hv hd hw hdw hwn W h O hO
  · intro W h O hO
    exact field_pb_zero _ hw hdw hwn' W h O hO

end GlobalTheory.KS.SquareField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_square_of_isGrpPullback {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by
  have hw : m ≫ G.hom = G'.hom ≫ f := h.1.w
  let a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  let b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  refine ⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Over.Hom.left (lift_fst a b)
  · exact congrArg Over.Hom.left (lift_snd a b)
  · rw [← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]
    have : lift a b ≫ (fst G G * snd G G) = a * b := by
      rw [MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left this
  · exact Over.w (lift a b)

theorem square_fibre_affine_opens : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap x₀) m → (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (P.A ⊗ P.A).left, IsSquare m m₂ ∧ m₂ ≫ (fst P.A P.A * snd P.A P.A).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧ m₂ ≫ (P.A ⊗ P.A).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧ IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧ (∀ W : P.A.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧ ∀ W W' : P.A.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  intro K _ P₀ R _ x₀ P m h
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  have hp : IsProper P.A.hom := P.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from P.A.left) := by
      rw [← terminal.comp_from P.A.hom]; infer_instance
    exact hW.inf hW'

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CechPrimitive
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Primitive

open GlobalTheory.KuennethOne

variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}

theorem rsT_eq_rs {O₀ O : A.Opens} (s : Γ(A, O₀)) (h : O ≤ O₀) : rsT s O = rs h s := by
  rw [rsT, dif_pos h]
  rfl

theorem pbT_eq (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀) :
    pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  exact dif_pos h

theorem rs_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀)
    (h' : O' ≤ O) : rs h' (pbT f s O) = pbT f s O' := by
  rw [pbT_eq f s h, pbT_eq f s (h'.trans h)]
  show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem app_pbT (r : T ⟶ Z) (f : Z ⟶ A) (g : T ⟶ A) (e : r ≫ f = g) {O₀ : A.Opens} (s : Γ(A, O₀))
    {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : (r.app O).hom (pbT f s O) = pbT g s (r ⁻¹ᵁ O) := by
  subst e
  rw [pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem le_pre_inf (f : T ⟶ A) {N : T.Opens} {V W : A.Opens} (h : N ≤ f ⁻¹ᵁ V) (h' : N ≤ f ⁻¹ᵁ W) :
    N ≤ f ⁻¹ᵁ (V ⊓ W) :=
  fun _ hx => ⟨h hx, h' hx⟩

private lemma pbT_add' (f : T ⟶ A) {O₀ : A.Opens} (s s' : Γ(A, O₀)) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O₀) : pbT f (s + s') N = pbT f s N + pbT f s' N := by
  simp only [pbT_eq f _ hN, map_add (f := _)]

private lemma pbT_rsT' (f : T ⟶ A) {O₀ O : A.Opens} (s : Γ(A, O₀)) (hO : O ≤ O₀) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O) : pbT f (rsT s O) N = pbT f s N := by
  rw [rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]
  show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem pbT_coc (hc : IsCoc U c) (f : T ⟶ A) (i j k : I) {N : T.Opens} (hi : N ≤ f ⁻¹ᵁ U i)
    (hj : N ≤ f ⁻¹ᵁ U j) (hk : N ≤ f ⁻¹ᵁ U k) :
    pbT f (c i j) N + pbT f (c j k) N = pbT f (c i k) N := by
  have hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := le_pre_inf f (le_pre_inf f hi hj) hk
  have l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN,
    ← pbT_add' f _ _ hN, hc i j k]

theorem exists_split (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by
  refine ⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩
  intro a b M ha hb
  have hg' : M ≤ g ⁻¹ᵁ U i₀ := le_top.trans hg
  have e1 := pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))
  have e2 := pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))
  have e3 := pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))
  have e4 := pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))
  have e5 := pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))
  have r1 := rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha
  have r2 := rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb
  have r3 := rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha
  have r4 := rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb
  simp only [map_sub, r1, r2, r3, r4]
  linear_combination e2 - e1 + e3 - e4 - e5

theorem iSup_triple (hU : ⨆ i, U i = ⊤) (m p q : Z ⟶ A) :
    ⨆ α : I × I × I, m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2 = ⊤ := by
  have cov : ∀ y : A, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, hi⟩ := cov (m x)
  obtain ⟨j, hj⟩ := cov (p x)
  obtain ⟨k, hk⟩ := cov (q x)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩

private lemma preimage_le_preimage_of_comp_eq {X₁ X₂ X₃ : Scheme.{0}} (s : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g : X₁ ⟶ X₃)
    (e : s ≫ m = g) {W : X₂.Opens} {O : X₃.Opens} (h : W ≤ m ⁻¹ᵁ O) : s ⁻¹ᵁ W ≤ g ⁻¹ᵁ O := by
  subst e
  intro x hx
  show (s ≫ m) x ∈ O
  rw [Scheme.Hom.comp_apply]
  exact h hx

private lemma presheaf_map_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) :
    (T.presheaf.map (homOfLE h').op).hom (pbT f s O) = pbT f s O' :=
  rs_pbT f s h h'

set_option maxHeartbeats 1600000 in
private theorem cech_coboundary_mul_sub_fst_sub_snd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) := by
  intro hL _ _ K _ P₀ I U c hU hc
  have : IsProper P₀.A.hom := P₀.isAb.proper
  have hsub : Subsingleton (𝟙_ (Over (Sp K))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let _ : Inhabited (𝟙_ (Over (Sp K))).left := inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))
  have hbij : Function.Bijective P₀.A.hom.appTop.hom := hL.globalFns _ P₀.A P₀.isAb
  let e : 𝟙_ (Over (Sp K)) ⟶ P₀.A := MonObj.one
  let g₀ : P₀.A.left ⟶ P₀.A.left := (toUnit P₀.A ≫ e).left
  let m := (fst P₀.A P₀.A * snd P₀.A P₀.A).left
  let p := (fst P₀.A P₀.A).left
  let q := (snd P₀.A P₀.A).left

  have hpt : ∀ x : P₀.A.left, g₀ x = e.left default := by
    intro x
    show ((toUnit P₀.A).left ≫ e.left) x = _
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨i₀, hi₀⟩ := cov (e.left default)
  have hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀ := fun x _ => by
    show g₀ x ∈ U i₀
    rw [hpt x]
    exact hi₀

  have es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (mul_one (𝟙 P₀.A))
  have es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀ := by
    rw [← Over.comp_left, lift_snd]
  have et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (one_mul (𝟙 P₀.A))
  have et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀ := by
    rw [← Over.comp_left, lift_fst]
  have et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  let V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens := fun α =>
    m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2
  have hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1 := fun α => inf_le_left.trans inf_le_left
  have hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1 := fun α => inf_le_left.trans inf_le_right
  have hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2 := fun α => inf_le_right
  obtain ⟨ψ, hK⟩ := kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance
    inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q)
    (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) -
      pbT q (c a.2.2 b.2.2) (V a ⊓ V b))
    (by
      intro a b d
      have w1 : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
      have w2 : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
      have w3 : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
      simp only [map_sub]
      rw [presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm b)) (inf_le_right.trans (hVm d))),
        presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp b)) (inf_le_right.trans (hVp d))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq b)) (inf_le_right.trans (hVq d))),
        presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm d))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp d))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq d)))]
      have cm := pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))
      have cp := pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))
      have cq := pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))
      linear_combination cm - cp - cq)
    (by
      let s := (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1)
        (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q _ es_q (hVq α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)))]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
    (by
      let s := (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2)
        (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p _ et_p (hVp α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), sub_right_comm]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
  unfold IsCob
  refine ⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩
  rw [rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]
  exact (neg_sub_neg _ _).symm

theorem cech_primitive : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) :=
  cech_coboundary_mul_sub_fst_sub_snd

end GlobalTheory.KS.Primitive
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Sym

private lemma pbT_rsT_eq_pbT_of_le_preimage {Y Z : Scheme.{0}} (n : Z ⟶ Y) {O₀ T : Y.Opens} (s : Γ(Y, O₀)) (hT : T ≤ O₀)
    {O : Z.Opens} (hO : O ≤ n ⁻¹ᵁ T) : pbT n (rsT s T) O = pbT n s O := by
  rw [← pbT_id s T, pbT_pbT n (𝟙 Y) (le_trans hT (le_of_eq rfl)) hO, Category.comp_id]

private lemma pbT_add_pbT_eq_pbT_add {Y Z : Scheme.{0}} (n : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT n s O + pbT n t O = pbT n (s + t) O := by
  unfold pbT
  split_ifs <;> simp

theorem pbT_coc {Y Z : Scheme.{0}} {I : Type} {U : I → Y.Opens} {c : C1 U} (hc : IsCoc U c) (n : Z ⟶ Y) (i j k : I)
    {O : Z.Opens} (hi : O ≤ n ⁻¹ᵁ U i) (hj : O ≤ n ⁻¹ᵁ U j) (hk : O ≤ n ⁻¹ᵁ U k) :
    pbT n (c i j) O + pbT n (c j k) O = pbT n (c i k) O := by
  have hT : O ≤ n ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := by
    intro x hx
    exact ⟨⟨hi hx, hj hx⟩, hk hx⟩
  rw [← pbT_rsT_eq_pbT_of_le_preimage n (c i j) (inf_le_left) hT, ← pbT_rsT_eq_pbT_of_le_preimage n (c j k) (le_trans (le_of_eq (by ac_rfl)) inf_le_right) hT,
    ← pbT_rsT_eq_pbT_of_le_preimage n (c i k) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) hT, pbT_add_pbT_eq_pbT_add, hc i j k]

theorem exists_square_data {K R : Type} [Field K] [CommRing R] {g : ℕ} {X X₂ Y Z : Scheme.{0}} {m : Y ⟶ X}
    {D : R → K} {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {π₀ π₁ π₂ : X₂ ⟶ X} {p₀ p₁ p₂ : Z ⟶ Y}
    (sq₀ : m₂ ≫ π₀ = p₀ ≫ m) (sq₁ : m₂ ≫ π₁ = p₁ ≫ m) (sq₂ : m₂ ≫ π₂ = p₂ ≫ m) {L : LB X} (hL : L.IsLB)
    {d₂ : L.ι → L.ι → ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)}
    (hd₂ : ∀ i j, LocDerK q₂ s₂ m₂ D (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j))
    {θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hφ : IsDlog m L dd φ) (hc : ∀ a, IsCoc _ (φ a))
    {w w' : Fin g → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hw : ∀ a, IsVF q₂ (w a)) (hw' : ∀ a, IsVF q₂ (w' a))
    (w₀ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₀ ⁻¹ᵁ V → w a O (pbT p₀ h O) = pbT p₀ (dd a V h) O)
    (w₁ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₁ ⁻¹ᵁ V → w a O (pbT p₁ h O) = pbT p₁ (dd a V h) O)
    (w₂ : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₂ ⁻¹ᵁ V → w a O (pbT p₂ h O) = 0)
    (w₀' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₀ ⁻¹ᵁ V → w' a O (pbT p₀ h O) = pbT p₀ (dd a V h) O)
    (w₂' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₂ ⁻¹ᵁ V → w' a O (pbT p₂ h O) = pbT p₂ (dd a V h) O)
    (w₁' : ∀ a (V : Y.Opens) (h : Γ(Y, V)) O, O ≤ p₁ ⁻¹ᵁ V → w' a O (pbT p₁ h O) = 0)
    (df : ∀ i i' j O, O ≤ π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j → ∀ f : Γ(X₂, O),
      d₂ i' j O f - d₂ i j O f = ∑ a, pbT p₁ (θ a i i') _ * w a _ (pbT m₂ f _))
    (df' : ∀ i j j' O, O ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') → ∀ f : Γ(X₂, O),
      d₂ i j' O f - d₂ i j O f = ∑ a, pbT p₂ (θ a j j') _ * w' a _ (pbT m₂ f _))
    (V : L.ι × L.ι × L.ι → Z.Opens)
    (hV : ∀ α, V α ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ L.U α.1 ⊓ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U α.2.1 ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U α.2.2)
    (prim : ∀ a, IsCob V (fun α β => pbT p₀ (φ a α.1 β.1) _ - pbT p₁ (φ a α.2.1 β.2.1) _ -
      pbT p₂ (φ a α.2.2 β.2.2) _)) :
    ∃ (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α))
      (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α)),
      (∀ i j, IsCoc _ (k i j)) ∧
      (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') ⊓ V α →
        rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) ∧
      (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') ⊓ V α →
        rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) ∧
      (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ⊓ V β →
        rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) ∧
      (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') ⊓ V α ⊓ V β →
        rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) := by
  classical
  choose b hb using prim
  have hQ : ∀ i j, p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ≤
      (𝟙 Z) ⁻¹ᵁ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) := by
    intro i j x hx
    have h1 : x ∈ (m₂ ≫ π₁) ⁻¹ᵁ L.U i := by rw [sq₁]; exact hx.1
    have h2 : x ∈ (m₂ ≫ π₂) ⁻¹ᵁ L.U j := by rw [sq₂]; exact hx.2
    exact And.intro h1 h2
  have hDer : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X), m₂ ≫ π = n ≫ m → ∀ i j,
      Der (n ≫ m) (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j)
        (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) :=
    fun n π h i j => der_tr (hd₂ i j) (𝟙 Z) π (by rw [Category.id_comp, h]) (hQ i j)
  have hC : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X) (sel : L.ι × L.ι × L.ι → L.ι), m₂ ≫ π = n ≫ m →
      (∀ α, V α ≤ (n ≫ m) ⁻¹ᵁ L.U (sel α)) → ∀ (i j : L.ι) (α β α₃ : L.ι × L.ι × L.ι),
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) +
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel β) (sel α₃)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) =
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel α₃)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)))
        ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) ⊓
          (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α₃)) := by
    intro n π sel h hs i j α β α₃
    have D := hDer n π h i j
    rw [D.rsT_dl L _ _ inf_le_left (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs β))),
      D.rsT_dl L _ _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs β))) (inf_le_right.trans (inf_le_right.trans (hs α₃))),
      D.rsT_dl L _ _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_left.trans inf_le_left)
        (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs α₃)))]
    exact D.dl_coc hL _ _ _ (inf_le_right.trans inf_le_left)
      (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans (hs α))))
      (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans (hs β))))
      (inf_le_right.trans (inf_le_right.trans (hs α₃)))
  have hs0 : ∀ α, V α ≤ (p₀ ≫ m) ⁻¹ᵁ L.U α.1 := fun α => (hV α).trans (inf_le_left.trans inf_le_left)
  have hs1 : ∀ α, V α ≤ (p₁ ≫ m) ⁻¹ᵁ L.U α.2.1 := fun α => (hV α).trans (inf_le_left.trans inf_le_right)
  have hs2 : ∀ α, V α ≤ (p₂ ≫ m) ⁻¹ᵁ L.U α.2.2 := fun α => (hV α).trans inf_le_right
  have hR : ∀ (n : Z ⟶ Y) (π : X₂ ⟶ X) (sel : L.ι × L.ι × L.ι → L.ι), m₂ ≫ π = n ≫ m →
      (∀ α, V α ≤ (n ≫ m) ⁻¹ᵁ L.U (sel α)) → ∀ (i j : L.ι) (α β : L.ι × L.ι × L.ι) (O : Z.Opens),
      O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) →
      rsT (dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β)
          ((p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β))) O =
        dl (n ≫ m) L (tr (𝟙 Z) m₂ π (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) (sel α) (sel β) O :=
    fun n π sel h hs i j α β O hO => (hDer n π h i j).rsT_dl L _ _ hO (inf_le_left.trans inf_le_left)
      (inf_le_left.trans (inf_le_right.trans (hs α))) (inf_le_right.trans (inf_le_right.trans (hs β)))
  have hB : ∀ (α β : L.ι × L.ι × L.ι) (O : Z.Opens), O ≤ V α ⊓ V β → ∀ a,
      pbT p₀ (φ a α.1 β.1) O - pbT p₁ (φ a α.2.1 β.2.1) O - pbT p₂ (φ a α.2.2 β.2.2) O =
        rsT (b a β) O - rsT (b a α) O := by
    intro α β O hOV a
    have h0V : V α ⊓ V β ≤ p₀ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.1 ⊓ m ⁻¹ᵁ L.U β.1) :=
      fun x hx => And.intro (hs0 α hx.1) (hs0 β hx.2)
    have h1V : V α ⊓ V β ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U β.2.1) :=
      fun x hx => And.intro (hs1 α hx.1) (hs1 β hx.2)
    have h2V : V α ⊓ V β ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U β.2.2) :=
      fun x hx => And.intro (hs2 α hx.1) (hs2 β hx.2)
    have := congrArg (fun s => rsT s O) (hb a α β)
    simp only [GlobalTheory.KS.Square.rsT_sub] at this
    rwa [GlobalTheory.KS.Square.rsT_pbT p₀ hOV h0V, GlobalTheory.KS.Square.rsT_pbT p₁ hOV h1V, GlobalTheory.KS.Square.rsT_pbT p₂ hOV h2V,
      GlobalTheory.KS.Square.rsT_rsT hOV inf_le_right, GlobalTheory.KS.Square.rsT_rsT hOV inf_le_left] at this
  refine ⟨fun i j α β =>
      dl (p₀ ≫ m) L (tr (𝟙 Z) m₂ π₀ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.1 β.1 _ -
        dl (p₁ ≫ m) L (tr (𝟙 Z) m₂ π₁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.2.1 β.2.1 _ -
        dl (p₂ ≫ m) L (tr (𝟙 Z) m₂ π₂ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j) (d₂ i j)) α.2.2 β.2.2 _,
    fun a j α => pbT p₂ (φ a α.2.2 j) _ - rsT (b a α) _,
    fun a i α => pbT p₁ (φ a α.2.1 i) _ - rsT (b a α) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j α β α₃
    simp only [GlobalTheory.KS.Square.rsT_sub]
    linear_combination hC p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β α₃ -
      hC p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β α₃ - hC p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β α₃
  · intro a j j' α O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hA : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hA' : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α := fun x hx => And.intro (hO hx).1.1 (hO hx).2
    have hB' : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j') :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    have hB'' : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    rw [GlobalTheory.KS.Square.rsT_pbT p₂ hA hB', GlobalTheory.KS.Square.rsT_pbT p₂ hA' hB'',
      GlobalTheory.KS.Square.rsT_rsT hA inf_le_right, GlobalTheory.KS.Square.rsT_rsT hA' inf_le_right]
    have c1 := pbT_coc (hc a) p₂ α.2.2 j j' (O := O) (fun x hx => hs2 α (hO hx).2) (fun x hx => (hO hx).1.1)
      (fun x hx => (hO hx).1.2)
    linear_combination -c1
  · intro a i i' α O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hA : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ V α := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hA' : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α := fun x hx => And.intro (hO hx).1.1 (hO hx).2
    have hB' : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i') :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    have hB'' : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    rw [GlobalTheory.KS.Square.rsT_pbT p₁ hA hB', GlobalTheory.KS.Square.rsT_pbT p₁ hA' hB'',
      GlobalTheory.KS.Square.rsT_rsT hA inf_le_right, GlobalTheory.KS.Square.rsT_rsT hA' inf_le_right]
    have c1 := pbT_coc (hc a) p₁ α.2.1 i i' (O := O) (fun x hx => hs1 α (hO hx).2) (fun x hx => (hO hx).1.1)
      (fun x hx => (hO hx).1.2)
    linear_combination -c1
  · intro i i' j α β O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hOi : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1.1 (hO hx).1.1.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1.1 (hO hx).1.1.2) (hO hx).2)
    have hOi' : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i' ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1.2 (hO hx).1.1.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1.2 (hO hx).1.1.2) (hO hx).2)
    rw [hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β O hOi, hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β O hOi,
      hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β O hOi, hR p₀ π₀ (fun α => α.1) sq₀ hs0 i' j α β O hOi',
      hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i' j α β O hOi', hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i' j α β O hOi']
    have hOV : O ≤ V α ⊓ V β := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hAα : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α := fun x hx => And.intro (hO hx).1.1.2 (hO hx).1.2
    have hAβ : O ≤ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β := fun x hx => And.intro (hO hx).1.1.2 (hO hx).2
    have hCα : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 α hx.2) hx.1
    have hCβ : p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U β.2.2 ⊓ m ⁻¹ᵁ L.U j) :=
      fun x hx => And.intro (hs2 β hx.2) hx.1
    simp only [GlobalTheory.KS.Square.rsT_pbT p₂ hAα hCα, GlobalTheory.KS.Square.rsT_pbT p₂ hAβ hCβ,
      GlobalTheory.KS.Square.rsT_rsT hAα inf_le_right, GlobalTheory.KS.Square.rsT_rsT hAβ inf_le_right]
    have hQ₀ : π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1.1 hx.2
    have hQ₀' : π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j ≤ π₁ ⁻¹ᵁ L.U i' ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1.2 hx.2
    have hT : m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j) ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') := by
      intro x hx
      have h1 : x ∈ (m₂ ≫ π₁) ⁻¹ᵁ (L.U i ⊓ L.U i') := hx.1
      rw [sq₁] at h1
      exact h1
    have hOQ : O ≤ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ π₂ ⁻¹ᵁ L.U j) := by
      intro x hx
      have h1 : x ∈ (p₁ ≫ m) ⁻¹ᵁ (L.U i ⊓ L.U i') := (hO hx).1.1.1
      have h2 : x ∈ (p₂ ≫ m) ⁻¹ᵁ L.U j := (hO hx).1.1.2
      rw [← sq₁] at h1
      rw [← sq₂] at h2
      exact And.intro h1 h2
    have E0 := dl_diff (hd₂ i j) (hd₂ i' j) sq₀ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 1
      (fun a V h O hO => by rw [w₀ a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.1 β.1 hOQ
      (fun x hx => hs0 α (hO hx).1.2) (fun x hx => hs0 β (hO hx).2)
    have E1 := dl_diff (hd₂ i j) (hd₂ i' j) sq₁ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 1
      (fun a V h O hO => by rw [w₁ a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.2.1 β.2.1 hOQ
      (fun x hx => hs1 α (hO hx).1.2) (fun x hx => hs1 β (hO hx).2)
    have E2 := dl_diff (hd₂ i j) (hd₂ i' j) sq₂ hQ₀ hQ₀' (fun a => θ a i i') hT hw (df i i' j) 0
      (fun a V h O hO => by rw [w₂ a V h O hO, Nat.cast_zero, MulZeroClass.zero_mul]) hφ α.2.2 β.2.2 hOQ
      (fun x hx => hs2 α (hO hx).1.2) (fun x hx => hs2 β (hO hx).2)
    have key : ∀ a, pbT p₁ (θ a i i') O * (pbT p₂ (φ a α.2.2 j) O - rsT (b a α) O - (pbT p₂ (φ a β.2.2 j) O - rsT (b a β) O)) =
        pbT p₁ (θ a i i') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₀ (φ a α.1 β.1) O) -
        pbT p₁ (θ a i i') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₁ (φ a α.2.1 β.2.1) O) -
        pbT p₁ (θ a i i') O * (((0 : ℕ) : Γ(Z, O)) * pbT p₂ (φ a α.2.2 β.2.2) O) := by
      intro a
      have c1 := pbT_coc (hc a) p₂ α.2.2 β.2.2 j (O := O) (fun x hx => hs2 α (hO hx).1.2)
        (fun x hx => hs2 β (hO hx).2) (fun x hx => (hO hx).1.1.2)
      have c2 := hB α β O hOV a
      push_cast
      linear_combination (-(pbT p₁ (θ a i i') O)) * (c1 + c2)
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linear_combination E0 - E1 - E2
  · intro i j j' α β O hO
    simp only [GlobalTheory.KS.Square.rsT_sub]
    have hOi : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.1) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.1) (hO hx).2)
    have hOi' : O ≤ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V α) ⊓ (p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ p₂ ⁻¹ᵁ m ⁻¹ᵁ L.U j' ⊓ V β) :=
      fun x hx => And.intro (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.2) (hO hx).1.2)
        (And.intro (And.intro (hO hx).1.1.1 (hO hx).1.1.2.2) (hO hx).2)
    rw [hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j α β O hOi, hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j α β O hOi,
      hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j α β O hOi, hR p₀ π₀ (fun α => α.1) sq₀ hs0 i j' α β O hOi',
      hR p₁ π₁ (fun α => α.2.1) sq₁ hs1 i j' α β O hOi', hR p₂ π₂ (fun α => α.2.2) sq₂ hs2 i j' α β O hOi']
    have hOV : O ≤ V α ⊓ V β := fun x hx => And.intro (hO hx).1.2 (hO hx).2
    have hAα : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α := fun x hx => And.intro (hO hx).1.1.1 (hO hx).1.2
    have hAβ : O ≤ p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V β := fun x hx => And.intro (hO hx).1.1.1 (hO hx).2
    have hCα : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V α ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U α.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 α hx.2) hx.1
    have hCβ : p₁ ⁻¹ᵁ m ⁻¹ᵁ L.U i ⊓ V β ≤ p₁ ⁻¹ᵁ (m ⁻¹ᵁ L.U β.2.1 ⊓ m ⁻¹ᵁ L.U i) :=
      fun x hx => And.intro (hs1 β hx.2) hx.1
    simp only [GlobalTheory.KS.Square.rsT_pbT p₁ hAα hCα, GlobalTheory.KS.Square.rsT_pbT p₁ hAβ hCβ,
      GlobalTheory.KS.Square.rsT_rsT hAα inf_le_right, GlobalTheory.KS.Square.rsT_rsT hAβ inf_le_right]
    have hQ₀ : π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j :=
      fun x hx => And.intro hx.1 hx.2.1
    have hQ₀' : π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ L.U j' :=
      fun x hx => And.intro hx.1 hx.2.2
    have hT : m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j')) ≤ p₂ ⁻¹ᵁ (m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U j') := by
      intro x hx
      have h1 : x ∈ (m₂ ≫ π₂) ⁻¹ᵁ (L.U j ⊓ L.U j') := hx.2
      rw [sq₂] at h1
      exact h1
    have hOQ : O ≤ m₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i ⊓ π₂ ⁻¹ᵁ (L.U j ⊓ L.U j')) := by
      intro x hx
      have h1 : x ∈ (p₁ ≫ m) ⁻¹ᵁ L.U i := (hO hx).1.1.1
      have h2 : x ∈ (p₂ ≫ m) ⁻¹ᵁ (L.U j ⊓ L.U j') := (hO hx).1.1.2
      rw [← sq₁] at h1
      rw [← sq₂] at h2
      exact And.intro h1 h2
    have E0 := dl_diff (hd₂ i j) (hd₂ i j') sq₀ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 1
      (fun a V h O hO => by rw [w₀' a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.1 β.1 hOQ
      (fun x hx => hs0 α (hO hx).1.2) (fun x hx => hs0 β (hO hx).2)
    have E1 := dl_diff (hd₂ i j) (hd₂ i j') sq₁ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 0
      (fun a V h O hO => by rw [w₁' a V h O hO, Nat.cast_zero, MulZeroClass.zero_mul]) hφ α.2.1 β.2.1 hOQ
      (fun x hx => hs1 α (hO hx).1.2) (fun x hx => hs1 β (hO hx).2)
    have E2 := dl_diff (hd₂ i j) (hd₂ i j') sq₂ hQ₀ hQ₀' (fun a => θ a j j') hT hw' (df' i j j') 1
      (fun a V h O hO => by rw [w₂' a V h O hO, Nat.cast_one, _root_.one_mul]) hφ α.2.2 β.2.2 hOQ
      (fun x hx => hs2 α (hO hx).1.2) (fun x hx => hs2 β (hO hx).2)
    have key : ∀ a, pbT p₂ (θ a j j') O * (pbT p₁ (φ a α.2.1 i) O - rsT (b a α) O - (pbT p₁ (φ a β.2.1 i) O - rsT (b a β) O)) =
        pbT p₂ (θ a j j') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₀ (φ a α.1 β.1) O) -
        pbT p₂ (θ a j j') O * (((0 : ℕ) : Γ(Z, O)) * pbT p₁ (φ a α.2.1 β.2.1) O) -
        pbT p₂ (θ a j j') O * (((1 : ℕ) : Γ(Z, O)) * pbT p₂ (φ a α.2.2 β.2.2) O) := by
      intro a
      have c1 := pbT_coc (hc a) p₁ α.2.1 β.2.1 i (O := O) (fun x hx => hs1 α (hO hx).1.2)
        (fun x hx => hs1 β (hO hx).2) (fun x hx => (hO hx).1.1.1)
      have c2 := hB α β O hOV a
      push_cast
      linear_combination (-(pbT p₂ (θ a j j') O)) * (c1 + c2)
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linear_combination E0 - E1 - E2

theorem exists_symm_of_ksCoc : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ) := by
  intro hLaws hLaws2 hGen K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hU hiso hks hφ
  classical
  obtain ⟨⟨m₂, hsqr, hm₀, hbase⟩, hsep, hpull, haff, hinter⟩ := square_fibre_affine_opens K P₀ R x₀ P m hpb
  have hmb : m ≫ P.A.hom = P₀.A.hom ≫ spMap x₀ := hpb.1.w
  have hdl := (DlogPol.dlog_independent K P₀ g v dd hv hdd P.A.left m L hL hiso).2 φ hφ
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    refine eq_top_iff.2 (fun x _ => ?_)
    have hx : m.base x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  choose w hw using fun a => SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a)
    (fst P₀.A P₀.A) (snd P₀.A P₀.A) (Or.inl ⟨rfl, rfl⟩)
  choose w' hw' using fun a => SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a)
    (snd P₀.A P₀.A) (fst P₀.A P₀.A) (Or.inr ⟨rfl, rfl⟩)
  have hvf : ∀ a, IsVF (P₀.A ⊗ P₀.A).hom (w a) :=
    fun a => ⟨(hw a).1, (hw a).2.1, (hw a).2.2.1, (hw a).2.2.2.1⟩
  have hvf' : ∀ a, IsVF (P₀.A ⊗ P₀.A).hom (w' a) :=
    fun a => ⟨(hw' a).1, (hw' a).2.1, (hw' a).2.2.1, (hw' a).2.2.2.1⟩
  have hPL := fun (W W' : P.A.left.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') =>
    ProdLift.main K R x₀ P.A P₀.A m m₂ D W W' hmb hsqr hW hW' _ rfl
  choose d₂ hd₂ using fun i j => (hPL (L.U i) (L.U j) (hU i) (hU j)).1 (d i) (d j) (hks.der i) (hks.der j)
  have df : ∀ i i' j O, O ≤ (fst P.A P.A).left ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ (snd P.A P.A).left ⁻¹ᵁ L.U j →
      ∀ f : Γ((P.A ⊗ P.A).left, O), d₂ i' j O f - d₂ i j O f =
        ∑ a, pbT (fst P₀.A P₀.A).left (θ a i i') _ * w a _ (pbT m₂ f _) :=
    fun i i' j O hO f => diff_prod x₀ (hks.der i) (hks.der i') (hks.der j) (hU i) (hU i') (hU j) hbase
      (hd₂ i j).1 (hd₂ i' j).1 hsqr.1 hsqr.2 inf_le_left inf_le_left inf_le_right inf_le_right
      (Q₀ := (fst P.A P.A).left ⁻¹ᵁ (L.U i ⊓ L.U i') ⊓ (snd P.A P.A).left ⁻¹ᵁ L.U j)
      (fun x hx => And.intro hx.1.1 hx.2) (fun x hx => And.intro hx.1.2 hx.2)
      (hd₂ i j).2.1 (hd₂ i j).2.2 (hd₂ i' j).2.1 (hd₂ i' j).2.2
      (hPL (L.U i ⊓ L.U i') (L.U j) (hinter _ _ (hU i) (hU i')) (hU j)).2
      (fun a => θ a i i') (fun f => hks.diff i i' _ le_rfl f) hvf
      (fun a => (hw a).2.2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.2) O hO f
  have df' : ∀ i j j' O, O ≤ (fst P.A P.A).left ⁻¹ᵁ L.U i ⊓ (snd P.A P.A).left ⁻¹ᵁ (L.U j ⊓ L.U j') →
      ∀ f : Γ((P.A ⊗ P.A).left, O), d₂ i j' O f - d₂ i j O f =
        ∑ a, pbT (snd P₀.A P₀.A).left (θ a j j') _ * w' a _ (pbT m₂ f _) :=
    fun i j j' O hO f => diff_prod x₀ (hks.der j) (hks.der j') (hks.der i) (hU j) (hU j') (hU i) hbase
      (hd₂ i j).1 (hd₂ i j').1 hsqr.2 hsqr.1 inf_le_right inf_le_right inf_le_left inf_le_left
      (Q₀ := (fst P.A P.A).left ⁻¹ᵁ L.U i ⊓ (snd P.A P.A).left ⁻¹ᵁ (L.U j ⊓ L.U j'))
      (fun x hx => And.intro hx.1 hx.2.1) (fun x hx => And.intro hx.1 hx.2.2)
      (hd₂ i j).2.2 (hd₂ i j).2.1 (hd₂ i j').2.2 (hd₂ i j').2.1
      (fun a b ha hb h1 h2 => (hPL (L.U i) (L.U j ⊓ L.U j') (hU i) (hinter _ _ (hU j) (hU j'))).2 a b ha hb h2 h1)
      (fun a => θ a j j') (fun f => hks.diff j j' _ le_rfl f) hvf'
      (fun a => (hw' a).2.2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.2) O hO f
  have prim := fun a => Primitive.cech_primitive hLaws hLaws2 hGen K P₀ L.ι (fun i => m ⁻¹ᵁ L.U i) (φ a) hcov (hdl.1 a)
  obtain ⟨k, e, e', hk, he, he', hki, hkj⟩ := exists_square_data hm₀ hsqr.1 hsqr.2 hL (fun i j => (hd₂ i j).1)
    hφ hdl.1 hvf hvf' (fun a => (hw a).2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.1) (fun a => (hw a).2.2.2.2.2.2)
    (fun a => (hw' a).2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.1) (fun a => (hw' a).2.2.2.2.2.2) df df' _
    (fun α => le_rfl) prim
  exact exists_isSymm_of_square K P₀.A.left (P₀.A ⊗ P₀.A).left P₀.A.hom (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left
    L.ι (fun i => m ⁻¹ᵁ L.U i) g θ φ hsep hpull (fun i => haff _ (hU i)) hdl.2 _ _ k e e'
    (Primitive.iSup_triple hcov _ _ _) hk he he' hki hkj

end GlobalTheory.KS.Sym
end

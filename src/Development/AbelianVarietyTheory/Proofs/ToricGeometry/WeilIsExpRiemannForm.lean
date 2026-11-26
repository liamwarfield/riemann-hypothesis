module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.WeilExp

theorem le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    (x : Z ⟶ Y) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k t _
    exact Set.mem_iInter.1 (h (Set.mem_univ t)) k
  · intro h t _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ t)

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

theorem translT_snd (x : T ⟶ A) :
    (Out.translT A x).left ≫ (snd T A).left = (Out.translPt A x).left := by
  rw [← Over.comp_left, Out.translT, lift_snd]

theorem translT_translPt_comm [IsCommMonObj A] (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translT A y).left ≫ (Out.translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show Out.translT A x ≫ ((fst T A ≫ y) * snd T A) = Out.translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, Out.translT, Out.translT, lift_snd, lift_snd, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_fst]
  exact mul_left_comm _ _ _

theorem lift_translPt {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translPt A x = (p ≫ x) * q := by
  show lift p q ≫ ((fst T A ≫ x) * snd T A) = _
  rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]

theorem lift_translT {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translT A x = lift p ((p ≫ x) * q) := by
  rw [Out.translT, comp_lift, lift_fst, lift_translPt]

end Transl

theorem exp_comm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (k : ℕ) (a b z : Fin g → ℂ) (E : ℤ)
    (hE : (E : ℝ) = (a ⬝ᵥ Hm.mulVec (star b)).im) :
    cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • a) ⬝ᵥ Hm.mulVec (star b)))) =
      cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star b)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • b) ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(2 * Real.pi * Complex.I) * (E : ℂ) / k) := by
  have h1 : b ⬝ᵥ Hm.mulVec (star a) = star (a ⬝ᵥ Hm.mulVec (star b)) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  have h2 : (E : ℂ) = ((a ⬝ᵥ Hm.mulVec (star b)).im : ℂ) := by
    rw [← hE]; simp
  have h3 := Complex.sub_conj (a ⬝ᵥ Hm.mulVec (star b))
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, h1, h2]
  congr 1
  rw [Complex.star_def]
  simp only [smul_eq_mul]
  push_cast at h3
  linear_combination (-(Real.pi : ℂ) * (k : ℂ)⁻¹) * h3

theorem cancel_frames {A₁ A₂ B₁ B₂ F₀ Fa Fb Fab Ca Cb e₁ e₂ e₃ e₄ c : ℂ} (ha : Fa ≠ 0) (hb : Fb ≠ 0)
    (hab : Fab ≠ 0) (h₁ : A₁ * Fa = Ca * e₁ * F₀) (h₂ : A₂ * Fab = Cb * e₂ * Fa)
    (h₃ : B₁ * Fb = Cb * e₃ * F₀) (h₄ : B₂ * Fab = Ca * e₄ * Fb) (he : e₁ * e₂ = e₃ * e₄ * c) :
    A₁ * A₂ = B₁ * B₂ * c := by
  have h₅ : A₁ * A₂ * Fab = Ca * Cb * (e₁ * e₂) * F₀ := by
    apply mul_right_cancel₀ ha
    linear_combination (A₂ * Fab) * h₁ + (Ca * e₁ * F₀) * h₂
  have h₆ : B₁ * B₂ * Fab = Ca * Cb * (e₃ * e₄) * F₀ := by
    apply mul_right_cancel₀ hb
    linear_combination (B₂ * Fab) * h₃ + (Cb * e₃ * F₀) * h₄
  apply mul_right_cancel₀ hab
  rw [h₅, he]
  linear_combination (-c) * h₆

section Values

variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv

theorem val_res {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)ˣ) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (res h f).val = valAt' x U f.val :=
  (hv X x).2.2.1 U V h f.val hx

theorem val_mul {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (f f' : Γ(X, U)ˣ) (hx : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U (f * f').val = valAt' x U f.val * valAt' x U f'.val := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U hx
  rw [he, he, he, Units.val_mul, map_mul]

theorem val_pull {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem val_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι) (x : Sp ℂ ⟶ Y)
    (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    valAt' x (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      valAt' x (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)).val *
        valAt' x (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)).val :=
  (val_mul hv x _ _ hx).trans (congrArg₂ (· * ·) (val_res hv x _ _ hx) (val_res hv x _ _ hx))

theorem val_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j) :
    valAt' x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valAt' (x ≫ h) (LB.wchart L φ j) (t.s j).val :=
  (val_res hv x _ _ hx).trans (val_pull hv x h _ _)

theorem val_constGen {A : Over (Sp ℂ)} [GrpObj A] (M : LB A.left) (V : (𝟙_ (Over (Sp ℂ))).left.Opens) (c : ℂˣ)
    (x : 𝟙_ (Over (Sp ℂ)) ⟶ Out.overRes V ⊗ A) (j : PEmpty → M.ι) :
    valAt' x.left _ ((Out.constGen A M (Out.unitRes V (unitOn c))).s j).val = c := by
  have hx : ⊤ ≤ x.left ⁻¹ᵁ LB.wchart M (Y := (Out.overRes V ⊗ A).left) (K := PEmpty) PEmpty.elim j :=
    (le_wchart_iff _ _ _ _).2 fun k => k.elim
  refine (val_res hv x.left _ _ hx).trans ?_
  refine (val_pull hv x.left (fst (Out.overRes V) A).left ⊤ _).trans ?_
  refine (val_pull hv _ V.ι ⊤ (unitOn c)).trans ?_
  have e : (x.left ≫ (fst (Out.overRes V) A).left) ≫ V.ι = 𝟙 (Sp ℂ) := by
    have : (x ≫ fst (Out.overRes V) A) ≫ Out.overResι V = 𝟙 _ := Subsingleton.elim _ _
    exact congrArg (·.left) this
  rw [e]
  have := (hv _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) ⊤ c le_top
  refine Eq.trans ?_ this
  congr 1

end Values

theorem weilIs_exp_riemannForm : Out.WeilSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a : u.Λ), 0 < k → ∀ (T : Over (Sp ℂ)) (p : (𝟙_ (Over (Sp ℂ)) ⟶ T)) (θ : Out.ThetaGrp P.A P.L k T), p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) → ∃ C : ℂ, ∀ (j : Fin 2 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1) → valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k = C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * u.fr (j 0) z ^ k) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) := by
  intro hW hv hext hred hth P u Hm χ Ef hAH k a b c hk hc p₀
  have := P.isAb.comm
  have := P.isAb.smooth
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have hpow : ∀ (n : ℕ) w, u.ex w ^ n = u.ex ((n : ℂ) • w) := by
    intro n w
    induction n with
    | zero => simp [hex0]
    | succ n ih => rw [pow_succ, ih, ← u.ex_add, Nat.cast_succ, add_smul, one_smul]
  have htor : ∀ l : u.Λ, u.ex ((k : ℂ)⁻¹ • (l : Fin P.g → ℂ)) ^ k = 1 := by
    intro l
    rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact (u.ker _).2 l.2
  obtain ⟨c', hc', -⟩ := (hW (Sp ℂ) P k (𝟙_ _)).1 _ _ (htor a) (htor b)
  obtain ⟨V, hV, hl, -⟩ := hc' p₀
  refine ⟨V, hV, hl, fun θx θy hx hy => ?_⟩
  intro j j' _ _ hjj
  have hsm : Smooth (Out.overRes V ⊗ P.A).hom := by
    rw [← Over.w (fst (Out.overRes V) P.A)]
    have h1 : Smooth (fst (Out.overRes V) P.A).left := by
      show Smooth (pullback.fst (Out.overRes V).hom P.A.hom)
      infer_instance
    have h2 : Smooth (Out.overRes V).hom := by
      show Smooth (V.ι ≫ 𝟙 _)
      infer_instance
    infer_instance
  apply Units.ext
  refine hext (Out.overRes V ⊗ P.A) (hred _ _ hsm) inferInstance _ _ _ fun x hxU => ?_
  have hxj := hxU.trans (x.left.preimage_mono inf_le_left)
  have hxj' := hxU.trans (x.left.preimage_mono inf_le_right)
  refine (val_res hv _ _ _ hxU).trans (Eq.trans ?_ (val_res hv _ _ _ hxU).symm)
  obtain ⟨z, hz⟩ := u.ex_onto (x ≫ snd _ _)
  obtain ⟨p, rfl⟩ : ∃ p, x = lift p (u.ex z) := ⟨x ≫ fst _ _, by rw [hz]; ext <;> simp⟩
  have hp : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, p ≫ Out.overResι V ≫ y = y := by
    intro y
    rw [← Category.assoc, Subsingleton.elim (p ≫ Out.overResι V) (𝟙 _), Category.id_comp]
  have hpx : p ≫ θx.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) := by rw [hx, hp]
  have hpy : p ≫ θy.pt = u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ)) := by rw [hy, hp]
  obtain ⟨Ca, hCa⟩ := hth P u Hm χ Ef hAH k a hk _ p θx hpx
  obtain ⟨Cb, hCb⟩ := hth P u Hm χ Ef hAH k b hk _ p θy hpy

  have tr : ∀ (θ : Out.ThetaGrp P.A P.L k (Out.overRes V)) (v : Fin P.g → ℂ), p ≫ θ.pt = u.ex v → ∀ w,
      (lift p (u.ex w)).left ≫ (Out.translT P.A θ.pt).left = (lift p (u.ex (w + v))).left ∧
      (lift p (u.ex w)).left ≫ (Out.translPt P.A θ.pt).left = (u.ex (w + v)).left := by
    intro θ v h w
    rw [← Over.comp_left, ← Over.comp_left, lift_translT, lift_translPt, h, ← u.ex_add, add_comm v w]
    exact ⟨rfl, rfl⟩
  have sn : ∀ w, (lift p (u.ex w)).left ≫ (snd (Out.overRes V) P.A).left = (u.ex w).left := by
    intro w
    rw [← Over.comp_left, lift_snd]
  have m := (le_wchart_iff _ _ _ _).1 hxj
  have m' := (le_wchart_iff _ _ _ _).1 hxj'
  have m₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j (.inl 0)) := by
    rw [← sn]; exact m (.inl 0)
  have m₂ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j (.inl 1)) := by
    rw [← (tr θx _ hpx z).2]; exact m (.inl 1)
  have m₃ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j' (.inl (.inl 1))) := by
    rw [← (tr θy _ hpy z).2]; exact m' (.inl (.inl 1))
  have m₄ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ
      P.L.U (j (.inr 1)) := by
    rw [← (tr θy _ hpy _).2, ← (tr θx _ hpx z).1, Category.assoc]; exact m (.inr 1)
  have e₁ : j (.inl 0) = j' (.inl (.inl 0)) := hjj _ _ rfl
  have e₂ : j (.inl 1) = j (.inr 0) := ‹LB.Coh P.L _ j› _ _ (translT_snd θx.pt).symm
  have e₃ : j' (.inl (.inl 1)) = j' (.inl (.inr 0)) := ‹LB.Coh P.L _ j'› _ _ (translT_snd θy.pt).symm
  have e₄ : j (.inr 1) = j' (.inl (.inr 1)) := hjj _ _ (translT_translPt_comm θx.pt θy.pt)
  have ec : z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) =
      z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := add_right_comm _ _ _
  have h₁ := hCa (j ∘ Sum.inl) z m₁ m₂
  have h₂ := hCb (j ∘ Sum.inr) _ (e₂ ▸ m₂ :) m₄
  have h₃ := hCb ((j' ∘ Sum.inl) ∘ Sum.inl) z (e₁ ▸ m₁ :) m₃
  have h₄ := hCa ((j' ∘ Sum.inl) ∘ Sum.inr) _ (e₃ ▸ m₃ :) (by rw [ec]; exact (e₄ ▸ m₄ :))
  simp only [Function.comp_apply] at h₁ h₂ h₃ h₄
  rw [← e₂] at h₂
  rw [← e₁] at h₃
  rw [← e₃, ← e₄, ec] at h₄
  have key := cancel_frames (pow_ne_zero k (u.fr_ne _ _ m₂)) (pow_ne_zero k (u.fr_ne _ _ m₃))
    (pow_ne_zero k (u.fr_ne _ _ m₄)) h₁ h₂ h₃ h₄
    (by rw [hc]; exact exp_comm Hm hAH.1 k a b z (Ef a b) (hAH.2.2.1 a b) : _ = _ * _ * (c : ℂ))
  have n₁ := (le_wchart_iff _ _ (j ∘ Sum.inr) _).2 fun i => m (.inr i)
  have n₂ := (le_wchart_iff _ _ (j' ∘ Sum.inl) _).2 fun i => m' (.inl i)
  have n₃ := (le_wchart_iff _ _ ((j' ∘ Sum.inl) ∘ Sum.inr) _).2 fun i => m' (.inl (.inr i))
  refine (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj).trans (Eq.trans ?_ (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj').symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (val_mulGen hv _ _ _ _ _ _ _ _ _ n₂)
    (val_constGen hv P.L V c _ _)).symm
  refine (congrArg (_ * ·) (val_pullGen hv _ _ _ _ _ _ _ n₁)).trans
    (Eq.trans ?_ (congrArg (_ * · * (c : ℂ)) (val_pullGen hv _ _ _ _ _ _ _ n₃).symm))
  rw [(tr θx _ hpx z).1, (tr θy _ hpy z).1]
  exact key

end GlobalTheory.WeilExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ComplexPointsGroup

def IsContFamily {T : Type} [TopologicalSpace T] {X : Scheme.{0}} (e : T → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)) (O : Set ℂ), IsOpen O → IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U ∧ valAt' (e t) U f ∈ O}

variable {T : Type} [TopologicalSpace T]

theorem IsContFamily.isOpen_mem {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens) :
    IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U} := by
  simpa using he U 0 Set.univ isOpen_univ

theorem IsContFamily.continuousOn {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens)
    (f : Γ(X, U)) : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ U} :=
  (continuousOn_open_iff (he.isOpen_mem U)).2 fun O hO => he U f O hO

variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv

theorem IsContFamily.comp {X Y : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (φ : X ⟶ Y) :
    IsContFamily (fun t => e t ≫ φ) := by
  intro U f O hO
  have := he (φ ⁻¹ᵁ U) ((φ.app U).hom f) O hO
  simp only [(hv X _).2.2.2.1] at this
  exact this

theorem isContFamily_of_affine {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)}
    (h : ∀ t₀, ∃ P : X.Opens, IsAffineOpen P ∧ ⊤ ≤ e t₀ ⁻¹ᵁ P ∧ IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ P} ∧
      ∀ g : Γ(X, P), ContinuousOn (fun t => valAt' (e t) P g) {t | ⊤ ≤ e t ⁻¹ᵁ P}) :
    IsContFamily e := by
  intro U f O hO
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ⟨hU, hf⟩
  obtain ⟨P, hP, h₀, hopen, hcont⟩ := h t₀
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, ((hv X _).1 U).1 hU⟩ (((hv X _).1 P).1 h₀)
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s (resG X hsU f)
  have key : ∀ t, ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s →
      valAt' (e t) U f = valAt' (e t) P g / valAt' (e t) P s ^ n := by
    intro t ht
    have hne := ((hv X (e t)).2.2.2.2.1 P s).1 ht
    obtain ⟨ev, hev⟩ := (hv X (e t)).2.1 _ ht
    have h1 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) g ht
    have h2 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) s ht
    have h3 := (hv X (e t)).2.2.1 U _ hsU f ht
    have hg' : resG X (X.basicOpen_le s) g = resG X (X.basicOpen_le s) s ^ n * resG X hsU f := hg
    rw [eq_div_iff (pow_ne_zero n hne), ← h1, ← h2, ← h3, hg', hev, hev, hev, map_mul, map_pow, mul_comm]
  have hN : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} =
      {t | ⊤ ≤ e t ⁻¹ᵁ P} ∩ (fun t => valAt' (e t) P s) ⁻¹' {0}ᶜ := by
    ext t
    constructor
    · intro ht
      exact ⟨le_trans ht ((e t).preimage_mono (X.basicOpen_le s)), ((hv X (e t)).2.2.2.2.1 P s).1 ht⟩
    · intro ht
      exact ((hv X (e t)).2.2.2.2.1 P s).2 ht.2
  have hNo : IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    rw [hN]
    exact (hcont s).isOpen_inter_preimage hopen isOpen_compl_singleton
  have hsub : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ⊆ {t | ⊤ ≤ e t ⁻¹ᵁ P} := by
    rw [hN]; exact Set.inter_subset_left
  have hc : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    refine ContinuousOn.congr (f := fun t => valAt' (e t) P g / valAt' (e t) P s ^ n) ?_ key
    exact ((hcont g).mono hsub).div (((hcont s).mono hsub).pow n)
      fun t ht => pow_ne_zero n (((hv X (e t)).2.2.2.2.1 P s).1 ht)
  refine ⟨{t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ∩ (fun t => valAt' (e t) U f) ⁻¹' O, ?_,
    hc.isOpen_inter_preimage hNo hO, ((hv X _).1 _).2 hs₀, hf⟩
  rintro t ⟨ht, hto⟩
  exact ⟨le_trans ht ((e t).preimage_mono hsU), hto⟩

theorem valAt'_appLE {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V h).hom f) = valAt' (x ≫ φ) U f := by
  rw [← (hv X x).2.2.2.1, ← (hv X x).2.2.1 _ V h _ hx]
  rfl

theorem isContFamily_of_isPullback {X Y S Z : Scheme.{0}} [IsAffine S] {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S}
    {iY : Z ⟶ Y} (H : IsPullback g iY iX f) {e : T → (Sp ℂ ⟶ Z)}
    (h₁ : IsContFamily (fun t => e t ≫ g)) (h₂ : IsContFamily (fun t => e t ≫ iY)) : IsContFamily e := by
  refine isContFamily_of_affine hv fun t₀ => ?_
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (e t₀ ≫ g) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := (e t₀ ≫ iY) (default : PrimeSpectrum ℂ)) trivial
  have hmem : ∀ t, ⊤ ≤ e t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) ↔ ⊤ ≤ (e t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (e t ≫ iY) ⁻¹ᵁ V := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)
  refine ⟨_, hP, (hmem t₀).2 ⟨((hv _ _).1 _).2 hpU, ((hv _ _).1 _).2 hpV⟩, ?_, fun r => ?_⟩
  · simp only [hmem]
    exact (h₁.isOpen_mem U).inter (h₂.isOpen_mem V)
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁.continuousOn U a).mono fun t ht => ((hmem t).1 ht).1).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
    · exact ((h₂.continuousOn V b).mono fun t ht => ((hmem t).1 ht).2).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
  | zero =>
    refine (continuousOn_const (c := (0 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_zero]
  | one =>
    refine (continuousOn_const (c := (1 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_add (f := _), Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_mul, Pi.mul_apply]


omit hv in
theorem continuous_iff_isContFamily {A : Over (Sp ℂ)} (e : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)) :
    Continuous[_, TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}] e ↔
      IsContFamily (X := A.left) (fun t => (e t).left) := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro h U f O hO
    exact h _ ⟨U, f, O, hO, rfl⟩
  · rintro h _ ⟨U, f, O, hO, rfl⟩
    exact h U f O hO

theorem isContFamily_lift {A B : Over (Sp ℂ)} {a : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)} {b : T → (𝟙_ (Over (Sp ℂ)) ⟶ B)}
    (ha : IsContFamily (X := A.left) (fun t => (a t).left)) (hb : IsContFamily (X := B.left) (fun t => (b t).left)) :
    IsContFamily (X := (A ⊗ B).left) (fun t => (lift (a t) (b t)).left) := by
  have H : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback A.hom B.hom
  refine isContFamily_of_isPullback hv H ?_ ?_
  · convert ha using 2 with t
    exact congrArg CommaMorphism.left (lift_fst (a t) (b t))
  · convert hb using 2 with t
    exact congrArg CommaMorphism.left (lift_snd (a t) (b t))

end GlobalTheory.ComplexPointsGroup

namespace GlobalTheory


open ComplexPointsGroup in
theorem isTopologicalGroup_complexPoints :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A], @IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}) _) := by
  intro hv A _
  let : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
  have hmul : ContinuousMul (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact (isContFamily_lift hv ((continuous_iff_isContFamily _).1 continuous_fst)
      ((continuous_iff_isContFamily _).1 continuous_snd)).comp hv μ[A].left⟩
  have hinv : ContinuousInv (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact ((continuous_iff_isContFamily _).1 continuous_id).comp hv (GrpObj.inv (X := A)).left⟩
  exact {}

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PointsCompact

abbrev ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

abbrev AffinePoints : Prop :=
  ∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f

abbrev pointTopology (X : Over (Sp ℂ)) : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ X) :=
  TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}

theorem continuous_of_affine (h1 : ValueRules) (X : Over (Sp ℂ)) (U : X.left.Opens)
    (hU : IsAffineOpen U) {Z : Type} [TopologicalSpace Z] (σ : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hσ : ∀ w, ⊤ ≤ (σ w).left ⁻¹ᵁ U)
    (hc : ∀ f : Γ(X.left, U), Continuous fun w => valAt' (σ w).left U f) :
    @Continuous _ _ _ (pointTopology X) σ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨V, f, O, hO, rfl⟩
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hwV, hwO⟩
  have hpU : (σ w).left (default : PrimeSpectrum ℂ) ∈ U := ((h1 _ (σ w).left).1 U).1 (hσ w)
  have hpV : (σ w).left (default : PrimeSpectrum ℂ) ∈ V := ((h1 _ (σ w).left).1 V).1 hwV
  obtain ⟨g, hgV, hpg⟩ := hU.exists_basicOpen_le ⟨_, hpV⟩ hpU
  letI := (X.left.presheaf.map (homOfLE <| X.left.basicOpen_le g).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen g
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (resG X.left hgV f)
  simp only [RingHom.algebraMap_toAlgebra] at ha

  have key : ∀ q : Sp ℂ ⟶ X.left, ⊤ ≤ q ⁻¹ᵁ X.left.basicOpen g →
      valAt' q V f * valAt' q U g ^ n = valAt' q U a := by
    intro q hq
    have hqU : ⊤ ≤ q ⁻¹ᵁ U := ((h1 _ q).1 U).2 (X.left.basicOpen_le g (((h1 _ q).1 _).1 hq))
    obtain ⟨e, he⟩ := (h1 _ q).2.1 _ hq
    obtain ⟨e', he'⟩ := (h1 _ q).2.1 _ hqU
    have := congrArg e ha
    rw [map_mul] at this
    rw [← (h1 _ q).2.2.1 V _ hgV f hq, ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) a hq,
      he, he, he', ← map_pow, ← he', ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) _ hq, he]
    simpa using this
  set F : Z → ℂ := fun w => valAt' (σ w).left U a / valAt' (σ w).left U g ^ n with hF
  have hopen : IsOpen {w | valAt' (σ w).left U g ≠ 0} := isOpen_ne_fun (hc g) continuous_const
  have hFc : ContinuousOn F {w | valAt' (σ w).left U g ≠ 0} :=
    (hc a).continuousOn.div ((hc g).pow n).continuousOn (fun w hw => pow_ne_zero _ hw)
  refine Filter.mem_of_superset ((hFc.isOpen_inter_preimage hopen hO).mem_nhds ?_) ?_
  · have hq : ⊤ ≤ (σ w).left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w).left).1 _).2 hpg
    have hne : valAt' (σ w).left U g ≠ 0 := ((h1 _ (σ w).left).2.2.2.2.1 U g).1 hq
    refine ⟨hne, ?_⟩
    show valAt' (σ w).left U a / valAt' (σ w).left U g ^ n ∈ O
    rw [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    exact hwO
  · rintro w' ⟨hne, hw'⟩
    have hq : ⊤ ≤ (σ w').left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w').left).2.2.2.2.1 U g).2 hne
    refine ⟨((h1 _ (σ w').left).1 V).2 (hgV (((h1 _ (σ w').left).1 _).1 hq)), ?_⟩
    have h' : valAt' (σ w').left U a / valAt' (σ w').left U g ^ n ∈ O := hw'
    rwa [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at h'

theorem exists_compact_of_affine (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ} (r : Fin n → Γ(X.left, U))
    (c : ℂ →+* Γ(X.left, U)) (hc : ∀ a, c a = constFn X.hom U a)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    ∃ C : Set (𝟙_ (Over (Sp ℂ)) ⟶ X), @IsCompact _ (pointTopology X) C ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U → (∀ j, ‖valAt' x.left U (r j)‖ ≤ 1) → x ∈ C := by
  letI := pointTopology X
  have hXw : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, x.left ≫ X.hom = 𝟙 _ := fun x => by
    simpa using Over.w x
  set K : Set (Fin n → ℂ) := {z | (∀ j, ‖z j‖ ≤ 1) ∧
    ∀ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), MvPolynomial.eval z p = 0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset ?_ ?_
    · have hKe : K = (⋂ j, {z : Fin n → ℂ | ‖z j‖ ≤ 1}) ∩
          ⋂ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), {z | MvPolynomial.eval z p = 0} := by
        ext z
        simp [hK]
      rw [hKe]
      refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_biInter fun p _ => ?_)
      · exact isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
      · exact isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    · intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 hz.1
  let e : K → (Γ(X.left, U) →+* ℂ) := fun z =>
    (MvPolynomial.eval₂Hom c r).liftOfSurjective hs ⟨MvPolynomial.eval z.1, fun p hp => z.2.2 p hp⟩
  have he : ∀ z : K, ∀ p, e z (MvPolynomial.eval₂Hom c r p) = MvPolynomial.eval z.1 p := fun z p =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hconst : ∀ z : K, ∀ a, e z (constFn X.hom U a) = a := fun z a => by
    rw [← hc, ← MvPolynomial.eval₂Hom_C c r a, he]
    simp
  have hex := fun z : K => (h2 X U hU (e z) (hconst z))
  choose σ hσ hσu using hex
  have hσc : Continuous σ := continuous_of_affine h1 X U hU σ (fun z => (hσ z).1) (fun f => by
    obtain ⟨p, rfl⟩ := hs f
    refine ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).congr fun z => ?_
    rw [(hσ z).2, he]
    rfl)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine ⟨Set.range σ, isCompact_range hσc, fun x hx hle => ?_⟩
  obtain ⟨ex, hex⟩ := (h1 _ x.left).2.1 U hx
  have hcomp : ex.comp (MvPolynomial.eval₂Hom c r) = MvPolynomial.eval (fun j => valAt' x.left U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
      rw [← hex, hc]
      exact (h1 _ x.left).2.2.2.2.2 X.hom (hXw x) U a hx
    · simp [hex]
  have hz : (fun j => valAt' x.left U (r j)) ∈ K := by
    refine ⟨hle, fun p hp => ?_⟩
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero]
  refine ⟨⟨_, hz⟩, ?_⟩
  refine (hσu ⟨_, hz⟩ x ⟨hx, fun f => ?_⟩).symm
  obtain ⟨p, rfl⟩ := hs f
  rw [he, ← hcomp, RingHom.comp_apply, hex]

theorem continuous_comp (h1 : ValueRules) {X Y : Over (Sp ℂ)} (φ : X ⟶ Y) :
    @Continuous _ _ (pointTopology X) (pointTopology Y) (fun x => x ≫ φ) := by
  letI := pointTopology X
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨U, f, O, hO, rfl⟩
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨φ.left ⁻¹ᵁ U, (φ.left.app U).hom f, O, hO, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Over.comp_left]
  rw [(h1 _ x.left).2.2.2.1 _ φ.left U f]
  exact Iff.rfl

theorem compact_of_sections (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (L : LB X.left) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (H : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
      ∃ r : Fin (M + 1) → Γ(X.left, Out.nonzeroLocus (s i)),
        (∀ j k, resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X.left (inf_le_left : Out.nonzeroLocus (s i) ⊓ L.U k ≤ _) (r j) *
          resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s i).f k)) ∧
        ∃ c : ℂ →+* Γ(X.left, Out.nonzeroLocus (s i)), (∀ a, c a = constFn X.hom _ a) ∧
          Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    @CompactSpace _ (pointTopology X) := by
  letI := pointTopology X
  choose hA r hr c hc hsurj using H
  have hC := fun i => exists_compact_of_affine h1 h2 X _ (hA i) (r i) (c i) (hc i) (hsurj i)
  choose C hCc hCmem using hC
  refine ⟨(isCompact_iUnion hCc).of_isClosed_subset isClosed_univ fun x _ => ?_⟩
  have hx0 : x.left (default : PrimeSpectrum ℂ) ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]; trivial
  unfold Out.nonzeroLocus at hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx0
  obtain ⟨i, k, hik⟩ := hx0
  set a : Fin (M + 1) → ℂ := fun j => valAt' x.left (L.U k) ((s j).f k) with ha
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => ‖a j‖)
  have hai : a i ≠ 0 := ((h1 _ x.left).2.2.2.2.1 _ _).1 (((h1 _ x.left).1 _).2 hik)
  have hai0 : a i0 ≠ 0 := by
    intro h0
    have := hi0 i
    rw [h0, norm_zero] at this
    exact hai (norm_le_zero_iff.1 this)
  have hb0 : ⊤ ≤ x.left ⁻¹ᵁ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).2.2.2.2.1 _ _).2 hai0
  have hmem0 : x.left (default : PrimeSpectrum ℂ) ∈ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).1 _).1 hb0
  have hN : ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus (s i0) := by
    refine ((h1 _ x.left).1 _).2 ?_
    unfold Out.nonzeroLocus
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hmem0⟩
  have hNk : ⊤ ≤ x.left ⁻¹ᵁ (Out.nonzeroLocus (s i0) ⊓ L.U k) :=
    ((h1 _ x.left).1 _).2 ⟨((h1 _ x.left).1 _).1 hN, X.left.basicOpen_le _ hmem0⟩
  refine Set.mem_iUnion.2 ⟨i0, hCmem i0 x hN fun j => ?_⟩
  have hrel : a j = valAt' x.left (Out.nonzeroLocus (s i0)) (r i0 j) * a i0 := by
    obtain ⟨e, he⟩ := (h1 _ x.left).2.1 _ hNk
    have := congrArg e (hr i0 j k)
    rw [map_mul, ← he, ← he, ← he, (h1 _ x.left).2.2.1 _ _ _ _ hNk, (h1 _ x.left).2.2.1 _ _ _ _ hNk,
      (h1 _ x.left).2.2.1 _ _ _ _ hNk] at this
    exact this
  have hle := hi0 j
  rw [hrel, norm_mul] at hle
  have hpos : 0 < ‖a i0‖ := norm_pos_iff.2 hai0
  nlinarith

theorem compactSpace_points_polAV : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ P : Out.PolAV (Sp ℂ), @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ P.A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ P.A) | ∃ (U : P.A.left.Opens) (f : Γ(P.A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})) := by
  intro h1 h2 P
  obtain ⟨A, grp, hab, g, hsm, L, hL, hrig, h9⟩ := P
  unfold Out.RelAmple at h9
  obtain ⟨N, hN, M, s, hcov, hh⟩ := h9 ⊤ (AlgebraicGeometry.isAffineOpen_top _)
  let X' : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  haveI : IsIso (⊤ : (Sp ℂ).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hψ : Function.Surjective (((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    have s1 := (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2
    have s2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
    exact s1.comp s2
  have hC : @CompactSpace _ (pointTopology X') := by
    refine compact_of_sections h1 h2 X' (Out.powOver A hsm ⊤ N) s hcov fun i => ?_
    obtain ⟨ha, r, hr1, hr2⟩ := hh i
    refine ⟨ha, r, hr1, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) ?_).hom.comp
      ((((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)), ?_, ?_⟩
    · exact le_top
    · intro a
      rfl
    · intro y
      obtain ⟨p, rfl⟩ := hr2 y
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ hψ p
      refine ⟨q, ?_⟩
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
      exact (MvPolynomial.eval₂_map _ _ _ _).symm
  let φ : X' ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι _ _).symm
  letI := pointTopology X'
  letI := pointTopology A
  have hsurj : Function.Surjective (fun y : 𝟙_ (Over (Sp ℂ)) ⟶ X' => y ≫ φ) := by
    intro x
    have hr : Set.range x.left.base ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι.base := by
      rw [Scheme.Opens.range_ι]
      intro y _
      trivial
    let y0 := IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hr
    have hy0 : y0 ≫ (A.hom ⁻¹ᵁ ⊤).ι = x.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk y0 ?_, ?_⟩
    · show y0 ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι = _
      rw [morphismRestrict_ι, ← Category.assoc, hy0]
      exact Over.w x
    · ext1
      exact hy0
  exact hsurj.compactSpace (continuous_comp h1 φ)

end GlobalTheory.PointsCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.KrullDimLEAndIsLocalRingQuotientPow
section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfMemPowMaximal
namespace GlobalTheory.EqZeroOfMemMaximalPow

theorem eq_zero_of_mem_pow_maximal {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  by_contra hy
  have hJ : LinearMap.ker (LinearMap.toSpanSingleton R R y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hmem : y ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · have hi := h (⟨m, hm⟩, i)
      simpa [smul_eq_mul, Ideal.mul_top] using hi
  obtain ⟨⟨r, hr⟩, hry⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m y).mp hmem
  have hJr : (1 - r) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, one_smul]
    exact sub_eq_zero.mpr hry.symm
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hle hJr) hr
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory.EqZeroOfMemMaximalPow
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ArtinReduction

theorem eq_zero_of_forall_mem_pow {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (hy : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  first
  | exact @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | (apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal ..)

theorem krullDimLE_and_isLocalRing_quotient_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 2 1 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (q : T' ⟶ T) (x : T ⟶ A)
    (h : ∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) :
    ∃ c : LB.Gen (Out.translDiff A L (q ≫ x)), c.IsGen := by
  obtain ⟨c, hc⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) =
      ![(lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext i
    fin_cases i
    · change (q ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (q ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

end ArtinReduction


open ArtinReduction in
theorem translDiff_triv_of_artin_local :
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) := by
  intro A _ L hA _ h R _ _ hR x hx
  have := hA.proper
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  refine TorusLocal.pt_ext_of_quotients (A := ℂ) (C := R)
    (fun i : MaximalSpectrum R × ℕ => i.1.asIdeal ^ (i.2 + 1)) eq_zero_of_forall_mem_pow
    (B := A) fun i => ?_
  have := i.1.isMaximal
  obtain ⟨h1, h2⟩ := krullDimLE_and_isLocalRing_quotient_pow i.1.asIdeal i.2
  have h3 : Module.Finite ℂ (R ⧸ i.1.asIdeal ^ (i.2 + 1)) :=
    (Module.finite_iff_krullDimLE_zero ℂ _).2 h1
  exact (h _ h2 h3 _ (exists_isGen_translDiff_comp A L _ x hx)).trans (MonObj.comp_one _).symm

end GlobalTheory
end

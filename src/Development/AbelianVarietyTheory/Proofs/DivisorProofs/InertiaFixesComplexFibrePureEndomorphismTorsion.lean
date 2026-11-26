module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem pureLift_step : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  intro GM p hp R R₀ _ _ π hR hπ h2 g g' A B _ _ A₀ B₀ _ _ i j hA hgA hB hgB hi hj U V U₀ V₀ _ _ _ _ eU eV
    r s r' s' hU hV hu f₀ _ ef₀
  have h2' : RingHom.ker π ^ 2 = 0 := by rw [Ideal.zero_eq_bot]; exact h2
  obtain ⟨Hc, -, Hl⟩ := GM p hp R hR _ (GlobalTheory.Cris.divided₂ h2') (GlobalTheory.Cris.isDPNilpotent_squareZero h2') R₀ π hπ rfl
  set κ := GlobalTheory.Cris.divided₂ h2'
  have inj := (Hc.crysToDR_bijective hi hA hgA).1
  have key : ∀ d ∈ GlobalTheory.DeRham.liftFil κ hi, GlobalTheory.DeRham.push κ (spMap π) f₀ d ∈ GlobalTheory.DeRham.liftFil κ hj := by
    intro d hd
    have hd' : GlobalTheory.DeRham.crysToDR κ hi d ∈ GlobalTheory.DeRham.Fil A := hd
    have h1 : GlobalTheory.DeRham.push κ (spMap π) U₀ d = r • d := by
      apply inj
      rw [GlobalTheory.DeRham.crysToDR_push κ hi hi U₀ U eU, map_smul]
      exact hU.1 _ hd'
    have h3 : GlobalTheory.DeRham.push κ (spMap π) V₀ (GlobalTheory.DeRham.push κ (spMap π) f₀ d)
        = r • GlobalTheory.DeRham.push κ (spMap π) f₀ d := by
      have := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) U₀ f₀)
      have h4 := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) f₀ V₀)
      simp only [LinearMap.comp_apply] at this h4
      rw [← h4, ← GlobalTheory.DeRham.push_congr κ (spMap π) ef₀, this, h1, map_smul]
    show GlobalTheory.DeRham.crysToDR κ hj _ ∈ GlobalTheory.DeRham.Fil B
    refine IsPure.mem_Fil hV hu ?_
    rw [← GlobalTheory.DeRham.crysToDR_push κ hj hj V₀ V eV, h3, map_smul]
  obtain ⟨f, ⟨hf, ef⟩, uf⟩ := Hl g A₀ A i hi hA hgA g' B₀ B j hj hB hgB f₀ key
  refine ⟨f, hf, ef, ?_, fun f' hf' ef' => uf f' ⟨hf', ef'⟩⟩
  have e1 : i ≫ (U ≫ f).left = (U₀ ≫ f₀).left ≫ j := by
    simp only [Over.comp_left, ← Category.assoc, eU]
    simp only [Category.assoc, ef]
  have e2 : i ≫ (f ≫ V).left = (U₀ ≫ f₀).left ≫ j := by
    rw [Over.comp_left, ← Category.assoc, ef, Category.assoc, eV, ← Category.assoc, ← Over.comp_left, ← ef₀]
  exact Hl.unique hi hA hgA hj hB hgB (U₀ ≫ f₀) e1 e2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_endomorphism_hom_lift_square_zero : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  first | exact @GlobalTheory.pureLift_step | exact GlobalTheory.pureLift_step | (intros; apply GlobalTheory.pureLift_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodge
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTower

open ReciprocityTheory.ChartRestriction.G.Out (thick thickTrans thickObj thickMap thickTrans_comp)

theorem exists_end {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : G' ⟶ G', IsMonHom U ∧ U.left ≫ φ = φ ≫ W.left := by
  let U : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ W.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have e : U.left ≫ φ = φ ≫ W.left := h.1.lift_fst _ _ _
  exact ⟨U, Out.PullGtPf.isMonHom_of_grpPullback h h W U e, e⟩

variable {T : Type} [CommRing T] (I : Ideal T)

theorem thickMap_fst (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ pullback.fst A.hom (thick T I (e + 1)) = pullback.fst A.hom (thick T I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_hom (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ (thickObj T I (e + 1) A).hom = (thickObj T I e A).hom ≫ thickTrans T I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (e : ℕ) (A : Over (Sp T)) [GrpObj A] :
    IsGrpPullback (thickObj T I e A) (thickObj T I (e + 1) A) (thickTrans T I e) (thickMap T I e A) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (thickTrans_comp T I e).symm (thickMap_fst I e A).symm) (thickMap_hom I e A)

theorem ker_factor_sq (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2
      = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  exact Ideal.mul_mem_mul hx (Ideal.pow_le_self (Nat.succ_ne_zero e) hy)

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

theorem isGrpPullback_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (e : ℕ) :
    IsGrpPullback (thickObj T I e A) G (spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp a))
      (pullback.fst A.hom (thick T I e) ≫ φ) :=
  ((isGrpPullback_pullback A _).comp h).congr (by rw [← Spec.map_comp]; rfl) rfl

theorem exists_end_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : ∀ e, thickObj T I e A ⟶ thickObj T I e A, (∀ e, IsMonHom (U e)) ∧
      (∀ e, (U e).left ≫ pullback.fst A.hom (thick T I e) ≫ φ = (pullback.fst A.hom (thick T I e) ≫ φ) ≫ W.left) ∧
      ∀ e, thickMap T I e A ≫ (U (e + 1)).left = (U e).left ≫ thickMap T I e A := by
  choose U hU eU using fun e => exists_end (isGrpPullback_red I h e) W
  refine ⟨U, hU, eU, fun e => (isGrpPullback_red I h (e + 1)).1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, eU, Category.assoc (U e).left, ← Category.assoc (thickMap T I e A),
      ← Category.assoc (thickMap T I e A), thickMap_fst, eU]
  · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, ← Category.assoc, Over.w]

theorem existsUnique_hom (hF : GlobalTheory.Published.FormalAlgebraisation) (hM : GlobalTheory.Published.GrothendieckMessing) {g : ℕ}
    (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (W : G ⟶ G) [IsMonHom W] {r s : S}
    (hW : IsPureBC G W r s) [IsNoetherianRing T] (hI : IsAdicComplete I T) {p : ℕ} (hp : p.Prime) (hpI : (p : T) ∈ I)
    {a b : S →+* T} (hab : ∀ x, a x - b x ∈ I) (hu : IsUnit (a r - b s)) {A B : Over (Sp T)} [GrpObj A] [GrpObj B]
    {φ : A.left ⟶ G.left} {ψ : B.left ⟶ G.left} (hA : IsGrpPullback A G (spMap a) φ)
    (hB : IsGrpPullback B G (spMap b) ψ) :
    ∃! F : A ⟶ B, IsMonHom F ∧ ∀ (X : Scheme.{0}) (x : X ⟶ A.left) (t : X ⟶ Sp (T ⧸ I ^ (0 + 1))),
      x ≫ A.hom = t ≫ thick T I 0 → x ≫ F.left ≫ ψ = x ≫ φ := by
  obtain ⟨U, hU, eU, cU⟩ := exists_end_red I hA W
  obtain ⟨V, hV, eV, cV⟩ := exists_end_red I hB W
  have rA := isGrpPullback_red I hA
  have rB := isGrpPullback_red I hB
  have e0 : (Ideal.Quotient.mk (I ^ (0 + 1))).comp a = (Ideal.Quotient.mk (I ^ (0 + 1))).comp b :=
    RingHom.ext fun x => Ideal.Quotient.eq.2 (by simpa using hab x)
  obtain ⟨f₀, hf₀, ef₀⟩ := grpPullback_iso (rA 0) ((rB 0).congr (by rw [e0]) rfl)
  let P : ℕ → Type := fun e => {f : thickObj T I e A ⟶ thickObj T I e B // IsMonHom f ∧ U e ≫ f = f ≫ V e}
  have step : ∀ (e : ℕ) (f : P e), ∃ f' : P (e + 1), thickMap T I e A ≫ f'.1.left = f.1.left ≫ thickMap T I e B ∧
      ∀ k : thickObj T I (e + 1) A ⟶ thickObj T I (e + 1) B, IsMonHom k →
        thickMap T I e A ≫ k.left = f.1.left ≫ thickMap T I e B → k = f'.1 := by
    intro e f
    have := f.2.1
    obtain ⟨k, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.pure_endomorphism_hom_lift_square_zero hM p hp _ _
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))
      ⟨e + 1 + 1, by
        rw [← map_natCast (Ideal.Quotient.mk (I ^ (e + 1 + 1))), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hpI _⟩
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) g g _ _ _ _ _ _
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rA (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rA (e + 1)).1 hg)
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rB (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rB (e + 1)).1 hg)
      (isGrpPullback_thickMap I e A) (isGrpPullback_thickMap I e B) (U (e + 1)) (V (e + 1)) (U e) (V e) (cU e) (cV e)
      _ _ _ _ (hW _ _ _ _ (rA (e + 1)) _ (eU _)) (hW _ _ _ _ (rB (e + 1)) _ (eV _))
      (by simpa using hu.map (Ideal.Quotient.mk (I ^ (e + 1 + 1)))) f.1 f.2.2
    exact ⟨⟨k, h₁, h₃⟩, h₂, h₄⟩
  choose nx h₁ h₂ using step
  have c₀ : U 0 ≫ f₀.hom = f₀.hom ≫ V 0 := Over.OverMorphism.ext ((rB 0).1.hom_ext
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ef₀, eU, eV, ← Category.assoc f₀.hom.left,
      ef₀]) (by rw [Over.w, Over.w]))
  let f : ∀ e, P e := fun e => Nat.rec ⟨f₀.hom, hf₀, c₀⟩ nx e
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := GlobalTheory.grpHom_algebraise hF.1 T I hI A B
    (PolPull.isAbelianScheme_of_isGrpPullback hG hA).proper (PolPull.isAbelianScheme_of_isGrpPullback hG hB).proper
    (fun e => thickObj T I e A) (fun e => thickObj T I e B) (fun e => thickMap T I e A) (fun e => thickMap T I e B)
    _ _ (fun e => isGrpPullback_pullback A _) (fun e => thickMap_fst I e A) (fun e => isGrpPullback_pullback B _)
    (fun e => thickMap_fst I e B) (fun e => (f e).1) (fun e => (f e).2.1) (fun e => h₁ e (f e))
  refine ⟨F, ⟨hF₁, fun X x t ht => ?_⟩, fun K ⟨hK, eK⟩ => hF₃ K fun e => ?_⟩
  · have h0 : pullback.fst A.hom (thick T I 0) ≫ F.left = f₀.hom.left ≫ pullback.fst B.hom (thick T I 0) := hF₂ 0
    rw [← pullback.lift_fst x t ht, Category.assoc, Category.assoc, ← Category.assoc _ F.left, h0, Category.assoc, ef₀]
  · have n : ∀ e, ((Over.pullback (thick T I e)).map K).left ≫ pullback.fst B.hom (thick T I e) =
        pullback.fst A.hom (thick T I e) ≫ K.left := fun e => pullback.lift_fst _ _ _
    have key : ∀ e, (Over.pullback (thick T I e)).map K = (f e).1 := by
      intro e
      induction e with
      | zero =>
        refine Over.OverMorphism.ext ((rB 0).1.hom_ext ?_ (by rw [Over.w, Over.w]))
        rw [← Category.assoc, n, Category.assoc, eK _ _ _ pullback.condition]
        exact ef₀.symm
      | succ e ih =>
        refine h₂ e (f e) _ inferInstance ?_
        rw [← ih]
        refine (isGrpPullback_pullback B (thick T I (e + 1))).1.hom_ext ?_ ?_
        · rw [Category.assoc, n, ← Category.assoc, thickMap_fst, Category.assoc, thickMap_fst, n]
        · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, thickMap_hom, ← Category.assoc, Over.w]
    rw [← key, n]

theorem exists_isGrpPullback_of_congr : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  intro hF hM S _ G _ g hG hg W _ r s hW T _ _ _ hI p hp hpI a b hab hu A _ φ hA
  have hB := isGrpPullback_pullback G (spMap b)
  have hba : ∀ x, b x - a x ∈ IsLocalRing.maximalIdeal T := fun x => by
    simpa using neg_mem (hab x)
  have un : ∀ y z : T, IsUnit y → z ∈ IsLocalRing.maximalIdeal T → IsUnit (y + z) := fun y z hy hz => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal y).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 h) hz) hy
  rw [map_sub] at hu
  have u₁ : IsUnit (a r - b s) := by simpa using un _ _ hu (hab s)
  have u₂ : IsUnit (b r - a s) := by
    have := un _ _ hu (hba r)
    rwa [add_comm, sub_add_sub_cancel] at this
  have u₃ : IsUnit (b r - b s) := by simpa using un _ _ u₂ (hab s)
  obtain ⟨F, ⟨hF₁, hF₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hab u₁ hA hB
  obtain ⟨K, ⟨hK₁, hK₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hba u₂ hB hA
  have FK : F ≫ K = 𝟙 A := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) hu hA hA).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hK₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hF₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  have KF : K ≫ F = 𝟙 _ := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) u₃ hB hB).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hF₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hK₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  refine ⟨F.left ≫ _, ((isGrpPullback_of_iso ⟨F, K, FK, KF⟩).comp hB).congr (Category.id_comp _) rfl,
    fun x hx => (hF₂ _ x (spMap (Ideal.Quotient.lift _ (IsLocalRing.residue T) fun y hy =>
      (IsLocalRing.residue_eq_zero_iff y).2 (by simpa using hy))) ?_).symm⟩
  rw [hx, ← Spec.map_comp]
  rfl

end GlobalTheory.PureTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodgeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_baseChanges_of_congruent_maps_pureHodge : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  first | exact @GlobalTheory.PureTower.exists_isGrpPullback_of_congr | exact GlobalTheory.PureTower.exists_isGrpPullback_of_congr | (intros; apply GlobalTheory.PureTower.exists_isGrpPullback_of_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrder
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionReduction

theorem eq_of_residue_eq : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  intro S _ P T _ _ b n hn x y hx hy hr
  letI := P.isAb.comm
  haveI : Smooth P.A.hom := P.isAb.smooth
  let j : Sp T ⟶ Sp S := spMap b
  let G : Over (Sp T) := (Over.pullback j).obj P.A
  have hn' : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  let m : G.left ⟶ G.left := (Out.mulA G n).left
  have hw : m ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified m := formallyUnramified_mulA (Sp T) G n hn'
  have h₂ : LocallyOfFiniteType (m ≫ G.hom) := by
    rw [hw]; dsimp [G]; infer_instance
  have h₃ : LocallyOfFiniteType m := locallyOfFiniteType_of_comp _ G.hom
  have e : (Over.pullback j).map (Out.mulA P.A n) = Out.mulA G n :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 P.A) n).trans
      (congrArg (· ^ n) (CategoryTheory.Functor.map_id (Over.pullback j) P.A))
  have mf : m ≫ pullback.fst P.A.hom j = pullback.fst P.A.hom j ≫ (Out.mulA P.A n).left := by
    change (Out.mulA G n).left ≫ _ = _
    rw [← e]; exact pullback.lift_fst _ _ _
  have kx : ∀ z : Over.mk (spMap b) ⟶ P.A, z ^ n = 1 → z.left ≫ (Out.mulA P.A n).left = j ≫ (η[P.A]).left := by
    intro z hz
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, hz, Hom.one_def]
    simp [j]
  let x' : Sp T ⟶ G.left := pullback.lift x.left (𝟙 _) (by simpa [j] using Over.w x)
  let y' : Sp T ⟶ G.left := pullback.lift y.left (𝟙 _) (by simpa [j] using Over.w y)
  have x₁ : x' ≫ pullback.fst P.A.hom j = x.left := pullback.lift_fst _ _ _
  have y₁ : y' ≫ pullback.fst P.A.hom j = y.left := pullback.lift_fst _ _ _
  have x₂ : x' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have y₂ : y' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have hab : x' ≫ m = y' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, mf, pullback.lift_fst_assoc, pullback.lift_fst_assoc, kx x hx, kx y hy]
    · rw [Category.assoc, Category.assoc]
      change x' ≫ m ≫ G.hom = y' ≫ m ≫ G.hom
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hc : spMap (IsLocalRing.residue T) ≫ x' = spMap (IsLocalRing.residue T) ≫ y' := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) x₁).trans
        (hr.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) y₁)).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (x₂.trans y₂.symm)).trans (Category.assoc _ _ _).symm)
  have hopen := isOpenImmersion_equalizer_ι_of_unramified m hab
  have hsub := range_subset_range_equalizer_ι _ hc
  have hcl : IsLocalRing.closedPoint T ∈ Set.range (equalizer.ι x' y') :=
    hsub ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue T)⟩
  have hall : Set.range (equalizer.ι x' y') = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (IsLocalRing.specializes_closedPoint p).mem_open (equalizer.ι x' y').isOpenEmbedding.isOpen_range hcl
  have hxy : x' = y' := eq_of_range_equalizer_ι_eq_univ m hab hall
  apply Over.OverMorphism.ext
  exact x₁.symm.trans ((congrArg (· ≫ pullback.fst P.A.hom j) hxy).trans y₁)

end GlobalTheory.TorsionReduction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrderStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  first | exact @GlobalTheory.TorsionReduction.eq_of_residue_eq | exact GlobalTheory.TorsionReduction.eq_of_residue_eq | (intros; apply GlobalTheory.TorsionReduction.eq_of_residue_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTransfer

theorem spMap_comp_of {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_completion (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮.IsMaximal) :
    ∃ (T : Formalism.L2.Pj.CDVR) (a : 𝓞 K →+* T.V) (j : T.V →+* ℂ), j.comp a = σ.comp (algebraMap (𝓞 K) K) ∧
      ∀ x, a x ∈ IsLocalRing.maximalIdeal T.V ↔ x ∈ 𝔮 := by
  let la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨𝔮, h𝔮.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 (RingOfIntegers.not_isField K)⟩
  obtain ⟨T, io, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨em, hem⟩ := GlobalTheory.ComplexEmbedding.exists_embedding_fractionField K σ T hfin io
  have hv : ∀ x : K, Formalism.L2.Pj.valV T.V (io x) = la.valuation K x := fun x => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hex : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io (algebraMap (𝓞 K) K x) := fun x =>
    GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (by
      rw [hv]; exact la.valuation_le_one x)
  choose f hf using hex
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨T, { toFun := f
               map_one' := hinj (by rw [hf, map_one, map_one, map_one])
               map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul, map_mul])
               map_zero' := hinj (by rw [hf, map_zero, map_zero, map_zero])
               map_add' := fun x y => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]) },
    em.comp (algebraMap T.V T.Fr), RingHom.ext fun x => ?_, fun x => ?_⟩
  · change em (algebraMap T.V T.Fr (f x)) = σ (algebraMap (𝓞 K) K x)
    rw [hf, ← hem]; rfl
  · change f x ∈ _ ↔ _
    rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), hf, hv]
    exact la.valuation_lt_one_iff_mem x

theorem pow_eq_one_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (y : Over.mk (𝟙 S') ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = y.left ≫ φ) (n : ℕ) : y ^ n = 1 ↔ z ^ n = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h (Over.mk (𝟙 S'))
  have key : ∀ {g : S' ⟶ S} (_ : g = f) (w : Over.mk g ⟶ G), w.left = z.left → (w ^ n = 1 ↔ z ^ n = 1) := by
    intro g hg w hw
    subst hg
    rw [Over.OverMorphism.ext hw]
  rw [← key (Category.id_comp f) (Φ y) ((hΦ y).trans e.symm), ← map_pow, MulEquiv.map_eq_one_iff]

noncomputable def restrict {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} (y : Over.mk (𝟙 S) ⟶ G) : Over.mk f ⟶ G :=
  (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 S)) ≫ y

theorem restrict_pow {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {y : Over.mk (𝟙 S) ⟶ G} {n : ℕ}
    (hy : y ^ n = 1) : restrict f y ^ n = 1 := by
  rw [restrict, ← MonObj.comp_pow, hy, MonObj.comp_one]

theorem exists_isGrpPullback_of_inertia : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  intro hFA hGM N _ P W _ r s hW q hq 𝔮 h𝔮 hq𝔮 hrs τ hτ A _ ψ hψ
  set i : 𝓞 N →+* ℂ := (algebraMap N ℂ).comp (algebraMap (𝓞 N) N) with hi
  have hinj : Function.Injective i := (algebraMap N ℂ).injective.comp (IsFractionRing.injective (𝓞 N) N)
  choose σ₀ hσ₀ hσ₁ using hτ
  have hσ : ∀ x, i (σ₀ x) = τ (i x) := hσ₀
  let σ : 𝓞 N →+* 𝓞 N :=
    { toFun := σ₀
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hσ, hσ, hσ, map_mul, map_mul])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add (f := _), hσ, hσ, hσ, map_add (f := _), map_add (f := _)]) }
  obtain ⟨T, a, j, hj, ha⟩ := exists_completion N (algebraMap N ℂ) 𝔮 h𝔮
  let b : 𝓞 N →+* T.V := a.comp σ
  have hab : ∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T.V := fun x => by
    have := (ha _).2 (𝔮.neg_mem (hσ₁ x))
    rwa [neg_sub, map_sub] at this
  have hqT : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := (ha _).2 hq𝔮
    rwa [map_natCast] at this
  have hu : IsUnit (a (r - s)) := by
    by_contra h
    exact hrs ((ha _).1 h)
  obtain ⟨B, _, φ, hφ⟩ : ∃ (B : Over (Sp T.V)) (_ : GrpObj B) (φ : B.left ⟶ P.A.left),
      IsGrpPullback B P.A (spMap a) φ := ⟨_, inferInstance, _, isGrpPullback_pullback P.A (spMap a)⟩
  obtain ⟨φ', hφ', hred⟩ := GlobalTheory.T.exists_iso_baseChanges_of_congruent_maps_pureHodge hFA hGM (𝓞 N) P.A P.g P.isAb P.smoothDim W r s hW T.V T.cpl q hq hqT a b
    hab hu B φ hφ
  have ea : spMap j ≫ spMap a = spMap i := spMap_comp_of hj
  have eb : spMap j ≫ spMap b = spMap (τ : ℂ →+* ℂ) ≫ spMap i :=
    (spMap_comp_of (RingHom.ext fun x => (RingHom.congr_fun hj (σ x)).trans (hσ x))).trans
      (spMap_comp_of (f := i) (g := (τ : ℂ →+* ℂ)) rfl).symm
  have er : spMap (IsLocalRing.residue T.V) ≫ spMap a = spMap (IsLocalRing.residue T.V) ≫ spMap b :=
    (spMap_comp_of (RingHom.ext fun x => Ideal.Quotient.eq.2 (hab x))).trans
      (spMap_comp_of (f := b) (g := IsLocalRing.residue T.V) rfl).symm
  have w₁ : ψ ≫ P.A.hom = (A.hom ≫ spMap j) ≫ spMap a := by rw [Category.assoc, ea, hψ.1.w]
  obtain ⟨χ, hχ₁, hχ₂⟩ : ∃ χ : A.left ⟶ B.left, χ ≫ φ = ψ ∧ χ ≫ B.hom = A.hom ≫ spMap j :=
    ⟨hφ.1.lift _ _ w₁, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  have hχ : IsGrpPullback A B (spMap j) χ := hφ.cancel (hψ.congr ea.symm hχ₁.symm) hχ₂
  have hc := (hχ.comp hφ').congr eb rfl
  have w₂ : (χ ≫ φ') ≫ P.A.hom = (A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap i := by rw [hc.1.w, Category.assoc]
  obtain ⟨io, hio₁, hio₂⟩ : ∃ io : A.left ⟶ A.left, io ≫ ψ = χ ≫ φ' ∧ io ≫ A.hom = A.hom ≫ spMap (τ : ℂ →+* ℂ) :=
    ⟨hψ.1.lift _ _ w₂, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  refine ⟨io, hψ.cancel (hc.congr rfl hio₁.symm) hio₂, fun n hn y hy x hx₁ hx₂ => ?_⟩
  have hnu : IsUnit (n : T.V) := by
    by_contra h
    have h' : (n : T.V) ∈ IsLocalRing.maximalIdeal T.V := h
    have hc : IsCoprime (q : T.V) (n : T.V) := by
      simpa using (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom T.V)
    obtain ⟨u, v, huv⟩ := hc
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ add_mem (Ideal.mul_mem_left _ u hqT) (Ideal.mul_mem_left _ v h')))
  have hyw : y.left ≫ P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w y
  have w₃ : (spMap a ≫ y.left) ≫ P.A.hom = 𝟙 (Sp T.V) ≫ spMap a := by
    rw [Category.assoc, hyw, Category.comp_id, Category.id_comp]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Sp T.V ⟶ B.left, t ≫ φ = spMap a ≫ y.left ∧ t ≫ B.hom = 𝟙 _ :=
    ⟨hφ.1.lift _ _ w₃, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  let yT : Over.mk (𝟙 (Sp T.V)) ⟶ B := Over.homMk t ht₂
  have hyT : yT ^ n = 1 := (pow_eq_one_iff hφ yT (restrict (spMap a) y) ht₁.symm n).2 (restrict_pow _ hy)
  let z : Over.mk (spMap b) ⟶ P.A := Over.homMk (t ≫ φ') (by
    change (t ≫ φ') ≫ P.A.hom = spMap b
    rw [Category.assoc, hφ'.1.w, reassoc_of% ht₂])
  have hz : z ^ n = 1 := (pow_eq_one_iff hφ' yT z rfl n).1 hyT
  have hzy : z = restrict (spMap b) y := GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order (𝓞 N) P T.V b n hnu z _ hz (restrict_pow _ hy) (by
    change spMap (IsLocalRing.residue T.V) ≫ t ≫ φ' = spMap (IsLocalRing.residue T.V) ≫ spMap b ≫ y.left
    rw [← Category.assoc, ← hred _ (by rw [Category.assoc, ht₂, Category.comp_id]), Category.assoc, ht₁,
      reassoc_of% er])
  have hzy' : t ≫ φ' = spMap b ≫ y.left := congrArg (fun u => u.left) hzy
  have hxχ : x ≫ χ = spMap j ≫ t := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, hχ₁, hx₂, Category.assoc, ht₁, reassoc_of% ea]
    · rw [Category.assoc, hχ₂, reassoc_of% hx₁, Category.assoc, ht₂, Category.comp_id]
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hio₁, reassoc_of% hxχ, hzy', reassoc_of% eb, Category.assoc, hx₂]
  · rw [Category.assoc, hio₂, reassoc_of% hx₁, Category.assoc, hx₁, Category.comp_id]

end GlobalTheory.InertiaTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  first | exact @GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | exact GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | (intros; apply GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia <;> assumption)
end

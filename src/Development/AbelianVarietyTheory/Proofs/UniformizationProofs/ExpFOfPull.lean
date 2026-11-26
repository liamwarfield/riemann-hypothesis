module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem expF_of_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s :=
  fun R _ _ D I A G _ _ U F _ _ k σ f t s hE hG hB =>
    GlobalTheory.UU.IntExp.expF_of_expT R I D A G U F k σ f t s hE hG hB

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullSecSval
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pullSec_sval {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun Z r z J hJ => ?_⟩
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans
    (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)

theorem whisker_famφT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by
  have hu : ρ ▷ D.P.A ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  fin_cases i
  · show (ρ ▷ D.P.A ≫ snd T D.P.A).left = (snd T' D.P.A).left
    rw [whiskerRight_snd]
  · show (ρ ▷ D.P.A ≫ padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (snd T' D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, whiskerRight_snd, ← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ D.c α).left = (toUnit (T' ⊗ D.P.A) ≫ D.c α).left
    rw [← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit (T' ⊗ D.P.A) ≫ η[D.P.A]).left
    rw [← Category.assoc, hu]

theorem expT_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → ∃ (σ' : U.SecGT T' k) (f' : ∀ α, SecBT D T' k α), U.ExpT T' k σ' f' ∧ PullT ρ f f' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T') (s : Raw D F k), PullB D F φ k f' s ↔ PullB D F (φ ≫ ρ) k f s := by
  intro R _ _ I D A G _ _ U T T' ρ k σ f H
  obtain ⟨σ', hσ⟩ := exists_pullSec_sval σ (ρ ▷ G).left (fun _ => (snd T' G).left) (fun _ => by
    show (ρ ▷ G ≫ snd T G).left = _
    rw [whiskerRight_snd])
  choose f' hf using fun α => exists_pullSec_sval (f α) (ρ ▷ D.P.A).left (famφT D T' α) (whisker_famφT D ρ α)
  have s1 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (snd T B).left = (snd T' B).left := fun B => by
    show (ρ ▷ B ≫ snd T B).left = _
    rw [whiskerRight_snd]
  have s2 : ∀ B : Over (Spec (CommRingCat.of R)), (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun B => by
    show (ρ ▷ B ≫ fst T B).left = (fst T' B ≫ ρ).left
    rw [whiskerRight_fst]
  refine ⟨σ', f', fun e => ?_, fun α Z r z J hJ => hf α Z r z J hJ, fun F _ _ φ s => ?_⟩
  · obtain ⟨s, hs⟩ := H e
    refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hJ => ?_⟩
    have := hs Z x (rG ≫ (ρ ▷ G).left) (rB ≫ (ρ ▷ D.P.A).left) (by rw [Category.assoc, s1, h1])
      (by rw [Category.assoc, s1, h2])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h3, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => (hf α Z rB z J hJ).trans (this.1 α hα), ?_⟩
    rw [hσ Z rG z JG hG, this.2]
    exact Finset.sum_congr rfl fun α _ => by rw [hf α Z rB z J hJ]
  · have e : (φ ▷ D.P.A).left ≫ (ρ ▷ D.P.A).left = ((φ ≫ ρ) ▷ D.P.A).left := by
      rw [comp_whiskerRight]; rfl
    have key : ∀ α (z : (DegPre.BF D F).left) J, Good D.P.L z J →
        sval (f' α) (φ ▷ D.P.A).left z J = sval (f α) ((φ ≫ ρ) ▷ D.P.A).left z J := fun α z J hJ =>
      (hf α _ (φ ▷ D.P.A).left z J hJ).trans (congrArg (fun q => sval (f α) q z J) e)
    exact ⟨fun h α z J hJ => (h α z J hJ).trans (key α z J hJ), fun h α z J hJ => (h α z J hJ).trans (key α z J hJ).symm⟩

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossIffOfIsActOf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.CrossTheta

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem cross_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (b : Y ⟶ Y) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k')))
    (H : ∀ y J, Good L y J → sval s₁ b y J * sval s₂' (𝟙 _) y J = sval s₂ b y J * sval s₁' (𝟙 _) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ (r ≫ b) z J * sval s₂' r z J = sval s₂ (r ≫ b) z J * sval s₁' r z J := by
  obtain ⟨I, hI, e⟩ := exists_good L hL (r z) (K := Bool) (fun c => cond c (b ≫ p) (𝟙 _ ≫ p))
    (fun c => J (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p))) (fun a c e => congrArg (fun q => J (r ≫ q)) e)
    (fun c => hJ (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p)))
  have v : ∀ (c : Y ⟶ Y) {m : ℤ} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => m))),
      I (c ≫ p) = J (r ≫ c ≫ p) → sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
    intro c m s hc
    rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
    exact gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _
  have h := congrArg (r.stalkMap z).hom (H (r z) I hI)
  rw [map_mul, map_mul, ← v b s₁ (e true), ← v b s₂ (e true), ← v (𝟙 _) s₁' (e false), ← v (𝟙 _) s₂' (e false),
    Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (a : A ⟶ A) [IsMonHom a] (x : T ⟶ A) :
    translT A x ≫ T ◁ a = T ◁ a ≫ translT A (x ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (a : A ⟶ A) [IsMonHom a] {k k' : ℤ} (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k' T) (hp : θ.pt = θ'.pt ≫ a)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A L k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A L k' T)}
    (h₁ : IsActOf A L k θ t₁ T₁) (h₂ : IsActOf A L k θ t₂ T₂) (h₁' : IsActOf A L k' θ' t₁' T₁')
    (h₂' : IsActOf A L k' θ' t₂' T₂') :
    (∀ y J, Good L y J → sval (L := L) t₁ (T ◁ a).left y J * sval (L := L) t₂' (𝟙 _) y J =
      sval (L := L) t₂ (T ◁ a).left y J * sval (L := L) t₁' (𝟙 _) y J) ↔
    (∀ y J, Good L y J → sval (L := L) T₁ (T ◁ a).left y J * sval (L := L) T₂' (𝟙 _) y J =
      sval (L := L) T₂ (T ◁ a).left y J * sval (L := L) T₁' (𝟙 _) y J) := by
  have c : (T ◁ a).left ≫ (translT A θ.pt).left = (translT A θ'.pt).left ≫ (T ◁ a).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}, Good L z J →
      (sval (L := L) T₁ (r ≫ (T ◁ a).left) z J * sval (L := L) T₂' r z J =
        sval (L := L) T₂ (r ≫ (T ◁ a).left) z J * sval (L := L) T₁' r z J ↔
      sval (L := L) t₁ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₂' (r ≫ (translT A θ'.pt).left) z J =
        sval (L := L) t₂ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₁' (r ≫ (translT A θ'.pt).left) z J) := by
    intro Z r z J hJ
    rw [ThetaPowOrder.act_sval h₁ _ z hJ, ThetaPowOrder.act_sval h₂ _ z hJ, ThetaPowOrder.act_sval h₁' _ z hJ,
      ThetaPowOrder.act_sval h₂' _ z hJ, Category.assoc, c, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L) t₂ _ z J), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J hJ
    have h := (key (𝟙 _) y hJ).2 (cross_val hL _ _ t₁ t₂ t₁' t₂' H _ y hJ)
    rwa [Category.id_comp] at h
  · intro H y J hJ
    have h := (key (translT A θ'.pt⁻¹).left y hJ).1 (cross_val hL _ _ T₁ T₂ T₁' T₂' H _ y hJ)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta

namespace GlobalTheory

theorem cross_iff_of_isActOf : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j j' : ℕ) (θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A.A A.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ a → ∀ (t₁ t₂ T₁ T₂ : SecA A F j) (t₁' t₂' T₁' T₂' : SecA A F j'), IsActOf A.A A.L j θ t₁ T₁ → IsActOf A.A A.L j θ t₂ T₂ → IsActOf A.A A.L j' θ' t₁' T₁' → IsActOf A.A A.L j' θ' t₂' T₂' → (Cross a t₁ t₂ t₁' t₂' ↔ Cross a T₁ T₂ T₁' T₂') := by
  intro _ R _ _ A F _ _ a ha j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  exact CrossTheta.cross_act A.isLB a θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionSingleValued

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep

theorem exists_indep_coords (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] [Algebra R F] [IsScalarTower R (FractionRing R) F] {Λ : Type} [Fintype Λ] (c : Λ → F) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → F) (a : Λ → κ → R), LinearIndependent R b ∧ ∀ i, c i = ∑ l, a i l • b l := by
  classical
  let B := Module.Basis.ofVectorSpace (FractionRing R) F
  let S := Finset.univ.biUnion fun i => (B.repr (c i)).support
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Λ × S => B.repr (c p.1) p.2)
  choose a ha using hd
  have hd0 : algebraMap R (FractionRing R) d ≠ 0 := (IsLocalization.map_units _ d).ne_zero
  refine ⟨S, inferInstance, fun l => (algebraMap R (FractionRing R) d)⁻¹ • B l, fun i l => a (i, l), ?_, fun i => ?_⟩
  · refine LinearIndependent.restrict_scalars' (K := FractionRing R) R ?_
    exact (B.linearIndependent.comp (fun l : S => l.1) Subtype.val_injective).units_smul
      (fun _ => (Units.mk0 _ hd0)⁻¹)
  · have h : ∀ l : S, a (i, l) • (algebraMap R (FractionRing R) d)⁻¹ • B l = B.repr (c i) l • B l := fun l => by
      rw [← algebraMap_smul (FractionRing R), ha, smul_smul, Algebra.smul_def (d : R), mul_right_comm,
        mul_inv_cancel₀ hd0, _root_.one_mul]
    simp only [h]
    rw [Finset.sum_coe_sort S (fun l => B.repr (c i) l • B l)]
    conv_lhs => rw [← B.linearCombination_repr (c i), Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (B.repr (c i)).support) (Finset.mem_univ i)) _
      (fun _ _ => zero_smul _ _)

theorem flat_germOf {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) :
    (germOf p x).Flat := by
  have e : germOf p x = (p.stalkMap x).hom.comp
      (((Sp R).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.ext fun c => by
      rw [germOf_apply, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  rw [e]
  refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) ?_) (Flat.stalkMap p x)
  have hU := isAffineOpen_top (Sp R)
  let _ := (Sp R).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
  have := hU.isLocalization_stalk ⟨p x, trivial⟩
  exact IsLocalization.flat ((Sp R).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp R).Opens)) : Sp R))
    (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl

theorem split_relation {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) {U : X.Opens} (hx : x ∈ U) {Λ κ : Type} [Fintype Λ] [Fintype κ]
    (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R) (s : Λ → Γ(X, U))
    (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ z, r z ∈ U →
        ∑ i, germOf q z (∑ l, a i l • b l) * gs r z U (s i) = 0) (l : κ) :
    ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i) = 0 := by
  let O : Type := X.presheaf.stalk x
  let : Algebra R O := (germOf p x).toAlgebra
  have : Module.Flat R O := flat_germOf p x
  have hi : LinearIndependent O (fun l => (1 : O) ⊗ₜ[R] b l) := Module.Flat.linearIndependent_one_tmul hb
  refine Fintype.linearIndependent_iff.1 hi (fun l => ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) ?_ l
  let eL : O →+* TensorProduct R O F := Algebra.TensorProduct.includeLeftRingHom
  let eR : F →+* TensorProduct R O F := (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := F)).toRingHom
  refine eq_zero_of_germOf (B := CommRingCat.of (TensorProduct R O F)) _ fun z => ?_
  have h := H (Spec (CommRingCat.of (TensorProduct R O F))) (Spec.map (CommRingCat.ofHom eR))
    ((Spec.map (CommRingCat.ofHom eL) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x) (by
      rw [Category.assoc, fromSpecStalk_comp]
      refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
      ext r
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := O) (B := F) r)) z (fromSpecStalk_mem x hx _)
  have e : ∑ l, (∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) • ((1 : O) ⊗ₜ[R] b l) =
      ∑ i, eR (∑ l, a i l • b l) * eL (gs (𝟙 X) x U (s i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_smul, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    show _ = ((1 : O) ⊗ₜ[R] (a i l • b l)) * ((gs (𝟙 X) x U (s i) : O) ⊗ₜ[R] (1 : F))
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
  · rw [gs_fromSpecStalk x hx]
    exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom eL) z _).symm

theorem gs_scal {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    (a : R) : gs r z ⊤ (scal p a) = germOf (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (germOf_apply _ _ _).symm

theorem gs_scal_comb {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    {U : X.Opens} (hz : r z ∈ U) {Λ : Type} [Fintype Λ] (a : Λ → R) (s : Λ → Γ(X, U)) :
    gs r z U (∑ i, resTop U (scal p (a i)) * s i) = ∑ i, germOf (r ≫ p) z (a i) * gs r z U (s i) := by
  rw [gs_fsum r z U hz]
  exact Finset.sum_congr rfl fun i _ => by rw [gs_mul r z U hz, gs_res r z le_top hz, gs_scal]

theorem sum_append {F O T : Type} [CommRing F] [CommRing O] (g : F →+* O) {n n' : ℕ} (c : Fin n → F) (c' : Fin n' → F)
    (t : Fin n → T) (t' : Fin n' → T) (v : T → O) :
    ∑ i, g (Fin.append c (-c') i) * v (Fin.append t t' i) =
      ∑ i, g (c i) * v (t i) - ∑ i, g (c' i) * v (t' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end ExpansionSingleValued


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep ExpansionSingleValued in
theorem expandsG_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : U.SecGF F k) (s s₂ : Fam D.toPre F k), U.ExpandsG F k σ s → U.ExpandsG F k σ s₂ → s = s₂ := by
  intro R _ _ I hR D A G _ _ U k F _ _ σ s s₂ ⟨n, c, τ, f, hE, hG, hB⟩ ⟨n', c', τ', f', hE', hG', hB'⟩
  let : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords R F (Fin.append c (-c'))
  have := U.smooth
  have hz : ∀ l α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (a i l)) * (Fin.append f f' i α).f j = 0 := fun l => by
    refine (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k _ (fun i => a i l) (Fin.append τ τ')
      (Fin.append f f') (fun i => ?_)).1 fun j => ?_
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hE i
      · simpa only [Fin.append_right] using hE' i
    refine fn_ext fun x hx => (gs_scal_comb G.hom (𝟙 _) x hx _ _).trans (Eq.trans ?_ (gs_zero _ _ _ hx).symm)
    rw [Category.id_comp]
    refine split_relation G.hom x hx b hb a (fun i => (Fin.append τ τ' i).f j) (fun Z q r hr z hz => ?_) l
    let ρ₀ : Z ⟶ pullback G.hom (jK R) := pullback.lift r (q ≫ jFK (R := R) F) (by rw [hr, Category.assoc, hj])
    let ρ : Z ⟶ (UnifPre.GF (G := G) F).left := pullback.lift q ρ₀ (pullback.lift_snd _ _ _).symm
    have e₁ : ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = q := pullback.lift_fst _ _ _
    have e₂ : ρ ≫ UnifPre.gFK (G := G) F = r :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom (jK R)) (pullback.lift_snd _ _ _)).trans
        (pullback.lift_fst _ _ _))
    obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Fin 1 => r ≫ 𝟙 _) j
      (fun u v _ => congrArg j (Subsingleton.elim u v)) (fun u => Set.mem_iInter.1 hz u)
    have h₁ := ExpGTrans.secLin_val hG ρ z hJ
    have h₂ := ExpGTrans.secLin_val hG' ρ z hJ
    simp only [gs_scal, e₂, sval_of _ r z J j eJ] at h₁ h₂
    simp only [← ha]
    refine (sum_append (germOf q z) c c' τ τ' (fun t => gs r z _ (t.f j))).trans (sub_eq_zero.2 ?_)
    rw [← e₁]
    exact h₁.symm.trans h₂
  refine fam_ext fun α => sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
  rw [ExpGTrans.secLin_val (hB α) _ y hJ, ExpGTrans.secLin_val (hB' α) _ y hJ]
  simp only [gs_scal]
  set q := 𝟙 _ ≫ (fst (TF (R := R) F) D.toPre.P.A).left
  set r := 𝟙 _ ≫ (DegPre.prB D.toPre F).left
  have e : r ≫ D.toPre.P.A.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [Category.assoc, Category.assoc, Over.w, ← hj]
    exact congrArg _ (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine sub_eq_zero.1 ((sum_append (germOf q y) c c' f f' (fun t => sval (t α) r y J)).symm.trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ha, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hm := hJ.mem (D.toPre.famφB α) r
  have h := (gs_scal_comb D.toPre.P.A.hom r y hm _ _).symm.trans
    ((congrArg _ (hz l α _)).trans (gs_zero _ _ _ hm))
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q y (b l))).symm.trans
    ((congrArg _ h).trans (mul_zero _)))
  rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q y _), _root_.mul_assoc]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.UU.IntGen

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ a.val * (val u' r z J).val := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      have := h U f
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, this, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have key : (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm)
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def basePts (T : Over (Spec (CommRingCat.of R))) (α mu : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cP D T α * cP D T mu).left, (cP D T α).left, (cP D T mu).left, (1 : T ⟶ D.P.A).left]

def baseExp (k : ℕ) : Fin 4 → ℤ := ![-1, 1, 1 - k, k - 1]

theorem prod_base {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (α mu : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ basePts D T α mu i) ^ baseExp k i =
      (h (cP D T' α * cP D T' mu).left)⁻¹ * h (cP D T' α).left * h (cP D T' mu).left ^ (1 - (k : ℤ)) *
        h (1 : T' ⟶ D.P.A).left ^ ((k : ℤ) - 1) := by
  have e₀ : ρ.left ≫ basePts D T α mu 0 = (cP D T' α * cP D T' mu).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (cP D _ α) (cP D _ mu)).trans (by rw [comp_cP, comp_cP]))
  have e₁ : ρ.left ≫ basePts D T α mu 1 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₂ : ρ.left ≫ basePts D T α mu 2 = (cP D T' mu).left := congrArg (fun q => q.left) (comp_cP D ρ mu)
  have e₃ : ρ.left ≫ basePts D T α mu 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 - (k : ℤ)) * _ ^ ((k : ℤ) - 1) = _
  rw [zpow_one, zpow_neg_one]

theorem exists_genT (T S : Over (Spec (CommRingCat.of R))) (π : T ⊗ D.P.A ⟶ S) (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D S α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k)), u₀.IsGen ∧
      ∀ (T' : Over (Spec (CommRingCat.of R))) (ρ : T' ⟶ T ⊗ D.P.A) (z : T'.left) (J), Good D.P.L z J →
        val u₀ ρ.left z J = cubN (th D z J) k (cP D T' α) (cP D T' mu) (ρ ≫ snd _ _) *
          (th D z J (cP D T' α) (ρ ≫ snd _ _) (cP D T' mu))⁻¹ * val v (ρ ≫ π).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) (α + k • mu) = a * mm ^ k := by rw [cPoint_add, cPoint_nsmul]
  have htr : trT D (toUnit T ≫ D.c mu) ≫ snd _ _ = x * mm :=
    (lift_snd _ _).trans (congrArg (x * ·) (comp_cP D (fst T D.P.A) mu))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu))
      (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := prod_base D π α mu k h
      have p₃ := prod_famT D (𝟙 (T ⊗ D.P.A)) (α + k • mu) k h
      have p₄ := prod_famT D (trT D (toUnit T ≫ D.c mu)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [htr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := Fin 4) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v π.left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  refine ⟨u₀, hu₀, fun T' ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D ρ α, ← comp_cP D ρ mu]

def multK (k : ℕ) (mu α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
    (GeneratorPullback.powGen D.P.L _ _ D.rigK k)

theorem gs_spec {Z : Scheme.{0}} (σ : Z ⟶ (TK R).left) (z : Z) (c : R) :
    gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
      gs σ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) c)) := by
  refine (gs_pull σ (jK R) z ⊤ trivial _).symm.trans (congrArg (gs σ z ⊤) ?_)
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem multK_frac (k : ℕ) (α mu : D.X)
    (v : LB.Gen (LB.LinComb D.P.L (basePts D (𝟙_ _) α mu) (baseExp k))) (hv : v.IsGen) :
    ∃ r₁ r₂ : R, r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (Z : Scheme.{0}) (σ : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₂) * (val (multK D k mu α) σ z J).val =
      gs (σ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r₁) *
        (val v (σ ≫ (toUnit (TK R)).left) z J).val := by
  obtain ⟨a, ha⟩ := exists_ratio D.P.isLB (u := multK D k mu α)
    (u' := LB.pullGen D.P.L _ _ v (toUnit (TK R)).left) (fun U _ h => by
      refine Eq.trans ?_ (prod_base D (toUnit (TK R)) α mu k h).symm
      have a₁ : ∀ χ, D.xK χ = (cP D (TK R) χ).left := fun χ => rfl
      have a₂ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [add_comm mu α, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) (pullGen_isGen _ _ _ _ hv _)
  let c : FractionRing R := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom c = a.val :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) a.val
  have hc0 : c ≠ 0 :=
    (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  obtain ⟨r₁, r₂, h₂, e⟩ := IsFractionRing.div_surjective (A := R) c
  have h₂' : r₂ ≠ 0 := nonZeroDivisors.ne_zero h₂
  have h₂K : algebraMap R (FractionRing R) r₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h₂'
  refine ⟨r₁, r₂, fun h => hc0 (by rw [← e, h, map_zero, zero_div]), h₂', fun Z σ z J hJ => ?_⟩
  have e' : algebraMap R (FractionRing R) r₁ = algebraMap R (FractionRing R) r₂ * c := by
    rw [← e, mul_div_cancel₀ _ h₂K]
  rw [ha Z σ z J hJ, val_pull hJ, gs_spec, gs_spec, e', map_mul, hc, ← _root_.mul_assoc]
  exact congrArg (· * _) (gs_mul σ z ⊤ trivial _ _).symm

theorem frac_mul {M : Type} [CommMonoid M] {g₁ g₂ : M} {u u₀ w m v : Mˣ} (h₁ : u = w * m) (h₂ : u₀ = w * v)
    (h : g₂ * m.val = g₁ * v.val) : g₂ * u.val = g₁ * u₀.val := by
  rw [h₁, h₂, Units.val_mul, Units.val_mul, mul_left_comm, h, mul_left_comm]

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α mu : D.X), ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k))) (r₁ r₂ : R), u₀.IsGen ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : TF (R := R) F ⟶ T) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → gs r z ⊤ (scal (DegPre.BF D F).hom r₂) * (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D F).hom r₁) * (val u₀ (r ≫ (φ ▷ D.P.A).left) z J).val := by
  intro hG R _ _ _ D T k α mu
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (basePts D (𝟙_ _) α mu) (baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_genT D T (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := multK_frac D k α mu v hv
  refine ⟨u₀, r₁, r₂, hu₀, h₁, h₂, fun F _ _ φ u hu hc Z r z J hJ => ?_⟩
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D F).hom)
  let ρ : T' ⟶ DegPre.BF D F := Over.homMk r rfl
  let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
  have e₁ := (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc T' ρ z J hJ
  have e₂ := vu₀ T' (ρ ≫ φ ▷ D.P.A) z J hJ
  have e₃ : val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J = val (multK D k mu α) κ.left z J :=
    val_pull hJ _ _ _
  have e₄ := hr _ κ.left z J hJ
  have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D F).hom := Over.w κ
  have e₆ : κ.left ≫ (toUnit (TK R)).left = ((ρ ≫ φ ▷ D.P.A) ≫ toUnit _).left :=
    congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
  have e₇ : (ρ ≫ φ ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D F := by rw [Category.assoc, whiskerRight_snd]
  have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D F).hom c) =
      gs (r ≫ (DegPre.BF D F).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
    gs_pull r (DegPre.BF D F).hom z ⊤ trivial _
  rw [e₅, e₆] at e₄
  rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
  rw [e₇] at e₂
  rw [g, g]
  exact frac_mul e₁ e₂ e₄

end GlobalTheory.UU.IntGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
section -- merged from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.SeparatedSymmetricModel
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

section BaseChange

variable {S S' : Scheme.{0}} (p : S' ⟶ S)

def dn {G : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) :
    Over.mk (T.hom ≫ p) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom p) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

lemma dn_map {G G' : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) (f : G ⟶ G') :
    dn p (y ≫ (Over.pullback p).map f) = dn p y ≫ f := by
  ext
  have h : ((Over.pullback p).map f).left ≫ pullback.fst G'.hom p =
      pullback.fst G.hom p ≫ f.left := pullback.lift_fst _ _ _
  change (y.left ≫ ((Over.pullback p).map f).left) ≫ pullback.fst G'.hom p =
    (y.left ≫ pullback.fst G.hom p) ≫ f.left
  rw [Category.assoc, Category.assoc, h]

variable {G : Over S} [GrpObj G] [IsCommMonObj G]

instance isComm_baseChange : IsCommMonObj ((Over.pullback p).obj G) :=
  Functor.isCommMonObj_obj

lemma dn_padd {T : Over S'} (a b : T ⟶ (Over.pullback p).obj G) :
    dn p (padd _ a b) = padd G (dn p a) (dn p b) := by
  rw [padd, padd, Functor.obj.μ_def, ← Category.assoc, dn_map]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_fst, lift_fst, lift_fst]
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_snd, lift_snd, lift_snd]

lemma dn_pzero (T : Over S') : dn p (pzero ((Over.pullback p).obj G) T) = pzero G _ := by
  rw [pzero, pzero, Functor.obj.η_def, ← Category.assoc, dn_map]
  congr 1
  exact toUnit_unique _ _

lemma dn_foldr {T : Over S'} {n : ℕ} (x : Fin n → (T ⟶ (Over.pullback p).obj G))
    (l : List (Fin n)) :
    dn p (l.foldr (fun k acc => padd _ (x k) acc) (pzero _ T)) =
      l.foldr (fun k acc => padd G (dn p (x k)) acc) (pzero G _) := by
  induction l with
  | nil => exact dn_pzero p T
  | cons a l ih => simp only [List.foldr_cons]; rw [dn_padd, ih]

variable {H : Over S'} [GrpObj H] [IsCommMonObj H]

def dn3 (f : H ⟶ (Over.pullback p).obj G) : Over.mk ((G3 H).hom ≫ p) ⟶ G3 G :=
  lift (dn p (x3 H 0 ≫ f)) (lift (dn p (x3 H 1 ≫ f)) (dn p (x3 H 2 ≫ f)))

omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] in
lemma downThree_comp_proj (f : H ⟶ (Over.pullback p).obj G) (k : Fin 3) :
    dn3 p f ≫ x3 G k = dn p (x3 H k ≫ f) := by
  fin_cases k <;> simp [x3, dn3]

def bcMap (f : H ⟶ (Over.pullback p).obj G) [IsMonHom f] : CubeMap H G where
  F := (dn p f).left
  F3 := (dn3 p f).left
  e := p
  e_comm := by
    have h1 : eSec H ≫ (dn p f).left = (dn p (η[H] ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : η[H] ≫ f = pzero _ (𝟙_ (Over S')) := by
      rw [IsMonHom.one_hom, pzero, toUnit_unit, Category.id_comp]
    rw [h1, h2, dn_pzero, pzero, Over.comp_left, eSec]
    congr 1
  psum_comm := fun I => by
    have h1 : (psum H (x3 H) I).left ≫ (dn p f).left = (dn p (psum H (x3 H) I ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : (dn3 p f).left ≫ (psum G (x3 G) I).left = (dn3 p f ≫ psum G (x3 G) I).left := rfl
    rw [h1, h2]
    congr 1
    simp only [psum]
    rw [foldr_padd_comp, dn_foldr, ← foldr_padd_pre]
    simp only [downThree_comp_proj]


end BaseChange

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

variable {G} {S' : Scheme.{0}} {H : Over S'} [GrpObj H]

end Sym

section IsoPull

variable {X X' Y Y' : Scheme.{0}} (L : LB X) (M : LB X')

end IsoPull

section Generic

variable (R : Type) [CommRing R] [IsDomain R]

end Generic

section Levels

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev toG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : CubeMap (thickObj R I e G) G :=
  bcMap (thick R I e) (𝟙 (thickObj R I e G))

def toB {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) : CubeMap (thickObj R I e G) D.P.A :=
  haveI := j.q_hom
  bcMap (thick R I e) j.q




end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPreCompare

section General

variable {X₁ X₂ Y Y₁ Y₂ T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂}
  {K : Type} [Fintype K]

variable {w : LB.Iso (L.pull a) (M.pull b)} {ψ : K → (T ⟶ Y)} {ε : K → ℤ}
  {φ₁ : K → (Y₁ ⟶ X₁)} {s : LB.Gen (LB.LinComb L φ₁ ε)} {f₁ : T ⟶ Y₁}
  {φ₂ : K → (Y₂ ⟶ X₂)} {t : LB.Gen (LB.LinComb M φ₂ ε)} {f₂ : T ⟶ Y₂}

end General

section Rigid

variable {X X' T Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_ratio {M : LB X} (cov : ∀ x, ∃ j, x ∈ M.U j) {t t' : LB.Gen M} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι), r z ∈ M.U j →
      gm r z _ (t.s j) = gm r z ⊤ u * gm r z _ (t'.s j) := by
  obtain ⟨u, hu⟩ := glue_unit ⊤ M.U (fun _ => le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (cov x))
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, GtCoordCompare.gm_gen ht (𝟙 X) x hx.1 hx.2,
        GtCoordCompare.gm_gen ht' (𝟙 X) x hx.1 hx.2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨u, fun Z r z j hj => ?_⟩
  rw [← gm_res r z (le_top : M.U j ≤ ⊤) hj u, hu, map_mul, map_inv, inv_mul_cancel_right]

theorem exists_rigidified (hL : L.IsLB) (hL' : L'.IsLB) (π : X' ⟶ T) (σ : T ⟶ X') (hσ : σ ≫ π = 𝟙 T)
    (w₀ : LB.Iso L' (L.pull F)) (hw₀ : w₀.IsGen) (ρ' : LB.Gen (L'.pull σ)) (hρ' : ρ'.IsGen) {φ : Y ⟶ X}
    (ρ : LB.Gen (L.pull φ)) (hρ : ρ.IsGen) (h : T ⟶ Y) (e : σ ≫ F = h ≫ φ) :
    ∃ w : LB.Iso L' (L.pull F), w.IsGen ∧ PMaps w (K := PUnit) (fun _ => σ) (fun _ => φ) (fun _ => 1) ρ' ρ h := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w₀).1 hw₀) hL hL' ρ' hρ'
  have ex : ∀ g : T ⟶ X, g = h ≫ φ → ∃ t' : LB.Gen (L.pull g), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p,
      r z ∈ (L.pull g).U p → gm r z _ (t'.s p) = gm (r ≫ h) z ((L.pull φ).U p) (ρ.s p) := by
    rintro _ rfl
    exact ⟨LB.pullGen L _ _ ρ h, DVR.pullGen_isGen _ _ _ _ hρ h, fun Z r z p hp =>
      (gm_res r z _ hp _).trans (gm_pull r h z _ (mem_pull.2 (mem_pull₂.1 hp)) _)⟩
  obtain ⟨t', ht', hv'⟩ := ex _ e
  obtain ⟨u, hu⟩ := exists_ratio (M := L.pull (σ ≫ F)) (fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL (F (σ x))
    exact ⟨fun _ => j, mem_pull₂.2 hj⟩) ht' ht
  let w : LB.Iso L' (L.pull F) := ⟨fun p => res le_top (pullU π ⊤ u) * w₀.s p⟩
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w r z j k = gm (r ≫ π) z ⊤ u * gw w₀ r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) (GtCoordCompare.gm_res_pull_top r z π
      (V := (L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _ u))
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', (isGen_iff w₀).1 hw₀ Z r z j j' k k' hj hj' hk hk']
    exact mul_left_comm _ _ _
  · have m : r z ∈ (L.pull (σ ≫ F)).U p := mem_pull₂.2 (hp _)
    refine (hv' Z r z p m).symm.trans ((hu Z r z p m).trans ?_)
    refine (congrArg _ (hv Z r z p q m (Set.mem_iInter.2 hq))).trans ?_
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hw Z (r ≫ σ) z _ _ (hp _) (hq _),
      Category.assoc, hσ, Category.comp_id, _root_.mul_assoc]

end Rigid

section Cube

open GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {S S' : Scheme.{0}} (p : S' ⟶ S) {G : Over S} {H T : Over S'}

end Cube

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ}

variable {LG : RigLB G} {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G}
  {w : LB.Iso (LG.L.pull (fstG I e G).left) (D.P.L.pull g.pG.left)}
  {ph : LB.Iso (LG.L.pull (toG I e G).F) (D.P.L.pull (toB j).F)}

end Clauses

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {rA : LB.Gen (A.L.pull (eSec A.A))}

end Main

end GlobalTheory.UnifPreCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiRel_of_pullB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  intro R _ _ D F _ _ f s₀ h hψ χ T ρ κ y z J hJ
  have a := pullB_values R D F _ _ 1 f s₀ h χ T ρ y z J hJ
  have b := pullB_values R D F _ _ 1 f s₀ h 0 T ρ (y * cT D T χ) z J hJ
  have c := hψ χ T (ρ ≫ toUnit _) κ y z J hJ
  exact a.trans (c.trans (congrArg _ b.symm))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  first | exact @GlobalTheory.psiRel_of_pullB | exact GlobalTheory.psiRel_of_pullB | (intros; apply GlobalTheory.psiRel_of_pullB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem exists_isProdB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl

end GlobalTheory.UU
end

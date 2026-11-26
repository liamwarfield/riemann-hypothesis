module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlobalLift

open CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem weilIs_of_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) : WeilIs A L k θx.pt θy.pt c := by
  intro p
  obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
  exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
    commIsOf_change hG hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem weilIs_iff_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k θx.pt θy.pt c ↔ CommIsOf A L k θx θy c := by
  refine ⟨fun H => ?_, weilIs_of_commIsOf hG hA hL⟩
  obtain ⟨c₀, h₀⟩ := CommutatorPairing.exists_commIsOf hG hA hL θx θy
  rw [CommutatorPairing.weilIs_unique hG hA hL H (weilIs_of_commIsOf hG hA hL h₀)]
  exact h₀

theorem val_powGen {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by
  refine Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _
    (Finset.univ : Finset (Fin n))) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ
    (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)

def nval {T : Over S} (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J

theorem val_symGen {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J * nval ν r z J) *
      (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * nval ν r z J) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

theorem exists_neg_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (ν : LB.Gen (negLB A L k T)) (hν : ν.IsGen) :
    ∃ ν' : LB.Gen (negLB A L k T'), ν'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → nval ν' r z J = nval ν (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, whiskerRight_snd_assoc]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ hν _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem whisker_negT {T T' : Over S} (h : T' ⟶ T) : negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

theorem exists_symLift_pull (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (H : SymLift A L k n x θ) : ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q

theorem exists_symLift_empty (hL : L.IsLB) (n : ℕ) {T : Over S} [IsEmpty T.left] (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n x θ := by
  have he : ∀ {Q : Prop} (_ : (T ⊗ A).left), Q := fun y => isEmptyElim ((fst T A).left y)
  exact ⟨⟨x, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y⟩, rfl, corr_of_val hL fun y _ _ => he y,
    ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y, corr_of_val hL fun y _ _ => he y⟩


omit [GrpObj A] in
theorem exists_section {T : Over S} [Subsingleton T.left] {V : T.left.Opens} {p : T.left} (hp : p ∈ V) :
    ∃ h : T ⟶ overRes V, h ≫ overResι V = 𝟙 T := by
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  exact ⟨Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩

end GlobalTheory.GlobalLift

namespace GlobalTheory


open GlobalLift in
theorem weilIs_iff_commIsOf_and_lift_subsingleton : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ)) := by
  intro hG hlift hsym S P k T
  refine ⟨weilIs_iff_commIsOf hG P.isAb P.isLB, fun x hx hT => ?_⟩
  rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
  · obtain ⟨θ, H⟩ := exists_symLift_empty (k := (k : ℤ)) P.isLB k x
    exact ⟨θ, H.pt_eq, fun _ => H⟩
  by_cases hk : Odd k
  · obtain ⟨V, hp, θ, H⟩ := (hsym S P k hk T x hx).1 p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', H'⟩ := exists_symLift_pull P.isLB h H
    rw [← Category.assoc, e, Category.id_comp] at H'
    exact ⟨θ', H'.pt_eq, fun _ => H'⟩
  · obtain ⟨V, hp, θ, H⟩ := hlift S P k T x hx p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', e', -⟩ := CommPairing.exists_pull P.isLB h θ
    rw [H, ← Category.assoc, e, Category.id_comp] at e'
    exact ⟨θ', e', fun h => absurd h hk⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem nonempty_torusExtension_of_isGt {K : Type} [Field K] (E : SplitExt (Spec (.of K)))
    (G : Over (Spec (.of K))) [GrpObj G] (h : E.IsGt G) : Nonempty (TorusExtension G) := by
  obtain ⟨d⟩ := h
  have := E.free
  have := E.finite
  have := d.q_affine
  exact ⟨
    { X := E.X
      B := E.B
      isAbelian := E.isAbelian
      q := d.q
      q_hom := d.q_hom
      q_flat := d.q_flat
      q_surjective := d.q_surjective
      q_quasiCompact := inferInstance
      i := d.i
      i_hom := d.i_hom
      isKernel := d.isKernel }⟩

theorem isSemiAbelian_of_isGt : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G],
    E.IsGt G → IsSemiAbelian G := by
  intro S E G _ hc h
  obtain ⟨hs, hg⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  obtain ⟨d⟩ := h
  have := d.q_affine
  have := E.isAbelian.proper
  refine ⟨hc, hs, ?_, ?_, hg, fun Ω _ _ p => ?_⟩
  · rw [← Over.w d.q]
    infer_instance
  · rw [← Over.w d.q]
    infer_instance
  · exact nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC p E G d)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_splitExt_isGt_of_torusExtension :
    ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → ∃ E : SplitExt (Spec (CommRingCat.of K)), E.IsGt G := by
  intro K _ G _ _ ⟨T⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Spec (CommRingCat.of K)) T.X G T.B T.isAbelian T.q T.i
    T.q_hom T.i_hom T.q_flat T.q_surjective T.q_quasiCompact T.isKernel
  obtain ⟨d, -, -⟩ := h T.isAbelian
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLevels

theorem comm_eq {B U : Type} [CommGroup B] [CommGroup U] (v : B → B → B → U) (φ φ' ψ χ : B → U) (k : ℤ) (l : ℕ)
    (x y : B) (hv : ∀ a, v a x 1 * v a y x = v a y 1 * v a x y)
    (hA : ∀ w, φ (w * x) * φ 1 * v w y x ^ k = φ w * φ x * v w y 1 ^ k)
    (hB : χ y * ψ 1 * (∏ i ∈ Finset.range l, v (x ^ i) x 1) ^ k =
      χ 1 * ψ y * (∏ i ∈ Finset.range l, v (x ^ i) x y) ^ k)
    (hC : φ' x * φ 1 ^ l = φ' 1 * φ x ^ l) :
    χ 1 * φ' x * (φ' 1 * χ y)⁻¹ = ψ 1 * φ (x ^ l) * (φ 1 * ψ y)⁻¹ := by
  have key : ∀ n : ℕ, φ (x ^ n) * φ 1 ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x y) ^ k =
      φ 1 * φ x ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x 1) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have a := congrArg Additive.ofMul (hA (x ^ n))
      have b := congrArg Additive.ofMul (hv (x ^ n))
      have c := congrArg Additive.ofMul ih
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow] at a b c ⊢
      linear_combination (norm := module) a + c - k • b
  have a := congrArg Additive.ofMul (key l)
  have b := congrArg Additive.ofMul hB
  have c := congrArg Additive.ofMul hC
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv] at a b c ⊢
  linear_combination (norm := module) c - a - b

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)

def pt {Y : Over S} (a : Y ⟶ A) : FreeAbelianGroup (Y.left ⟶ A.left) := FreeAbelianGroup.of a.left

abbrev ValFam (Y : Over S) : Type 1 :=
  ∀ (Z : Over S) (_ : Z ⟶ Y) (z : Z.left) (_ : (Z.left ⟶ A.left) → L.ι), (Z.left.presheaf.stalk z)ˣ

def Rep {Y : Over S} (D : FreeAbelianGroup (Y.left ⟶ A.left)) (f : ValFam L Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∑ k, ε k • FreeAbelianGroup.of (φ k) = D ∧
      ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L z J → val t r.left z J = f Z r z J

variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}

omit [GrpObj A] in
theorem oneGen_isGen : (LB.oneGen L (Y := Y.left)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

omit [GrpObj A] in
theorem Rep.one : Rep L (Y := Y) 0 (fun _ _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, oneGen_isGen, Fintype.sum_empty _, fun _ _ _ _ _ => val_one _⟩

omit [GrpObj A] in
theorem Rep.mul (h : Rep L D f) (h' : Rep L D' f') : Rep L (D + D') (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hD, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hD', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_,
    fun Z r z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv Z r z J hJ) (hv' Z r z J hJ))⟩
  rw [Fintype.sum_sum_type, ← hD, ← hD']; rfl

omit [GrpObj A] in
theorem Rep.inv (h : Rep L D f) : Rep L (-D) (fun Z r z J => (f Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hD, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, ?_,
    fun Z r z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (hv Z r z J hJ))⟩
  rw [← hD]; simp

omit [GrpObj A] in
theorem Rep.congr (h : Rep L D f) (hD : D = D') (hf : ∀ Z r z J, f Z r z J = f' Z r z J) : Rep L D' f' := by
  obtain rfl : f = f' := by funext Z r z J; exact hf Z r z J
  exact hD ▸ h

omit [GrpObj A] in
theorem Rep.pow (h : Rep L D f) (n : ℕ) : Rep L (n • D) (fun Z r z J => f Z r z J ^ n) := by
  induction n with
  | zero => exact Rep.one.congr (zero_smul _ _).symm (fun _ _ _ _ => (pow_zero _).symm)
  | succ n ih => exact (ih.mul h).congr (succ_nsmul _ _).symm (fun _ _ _ _ => (pow_succ _ _).symm)

omit [GrpObj A] in
theorem Rep.zpow (h : Rep L D f) (n : ℤ) : Rep L (n • D) (fun Z r z J => f Z r z J ^ n) := by
  cases n with
  | ofNat n => exact (h.pow n).congr (by simp) (fun _ _ _ _ => by simp)
  | negSucc n => exact (h.pow (n + 1)).inv.congr (negSucc_zsmul _ _).symm (fun _ _ _ _ => (zpow_negSucc _ _).symm)

theorem Rep.theta {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (s : Y ⟶ T) (a : Y ⟶ A) :
    Rep L (k • pt a - k • pt ((s ≫ θ.pt) * a)) (fun Z r z J => thetaVal θ (r ≫ s) (r ≫ a) z J) := by
  refine ⟨Fin 2, inferInstance, _, _, LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
    (lift s a).left, DVR.pullGen_isGen _ _ _ _ θ.isGen _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_theta (k := k) θ.pt s a (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul] at this
    rw [this, neg_smul, ← sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift]; rfl

def cubeVal (t : LB.Gen (Theta A L)) {Z : Over S} (z : Z.left) (J : (Z.left ⟶ A.left) → L.ι) (a b c : Z ⟶ A) :
    (Z.left.presheaf.stalk z)ˣ := val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift a (lift b c)).left z J

theorem Rep.cube [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (a b c : Y ⟶ A) :
    Rep L (pt (a * b * c) - pt (a * b) - pt (a * c) - pt (b * c) + pt a + pt b + pt c - pt (1 : Y ⟶ A))
      (fun Z r z J => cubeVal t z J (r ≫ a) (r ≫ b) (r ≫ c)) := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left,
    DVR.pullGen_isGen _ _ _ _ ht _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_cub a b c (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv] at this
    rw [this]; simp only [sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl

theorem Rep.cubeProd [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (x c : Y ⟶ A) (n : ℕ) :
    Rep L (pt (x ^ n * c) - pt c - pt (x ^ n) + pt (1 : Y ⟶ A) + n • (pt x + pt c - pt (x * c) - pt (1 : Y ⟶ A)))
      (fun Z r z J => ∏ i ∈ Finset.range n, cubeVal t z J ((r ≫ x) ^ i) (r ≫ x) (r ≫ c)) := by
  induction n with
  | zero => exact Rep.one.congr (by simp) (fun _ _ _ _ => by simp)
  | succ n ih =>
    refine (ih.mul (Rep.cube ht (x ^ n) x c)).congr ?_ (fun _ _ _ _ => ?_)
    · rw [pow_succ, succ_nsmul]; abel
    · rw [Finset.prod_range_succ, MonObj.comp_pow]

theorem Rep.rigid (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {Z : Over S}
    {D : FreeAbelianGroup ((Z ⊗ A).left ⟶ A.left)} {f : ValFam L (Z ⊗ A)} (h : Rep L D f) (hD : D = 0)
    (a : Z ⟶ A) {z : Z.left} {J} (hJ : Good L z J) : f Z (lift (𝟙 Z) a) z J = f Z (lift (𝟙 Z) 1) z J := by
  obtain ⟨K, _, φ, ε, t, ht, hD', hv⟩ := h
  obtain ⟨c, hc⟩ := exists_ratio hL (φ := φ) (ε := ε) (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ g => by
      have := congrArg (FreeAbelianGroup.lift (fun q => Additive.ofMul (g q))) (hD'.trans hD)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of, map_zero] at this
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      apply Additive.ofMul.injective
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using this)
    (fst Z A).left (lift (𝟙 Z) 1).left (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA Z) ht oneGen_isGen
  rw [← hv _ _ z J hJ, ← hv _ _ z J hJ, hc _ _ z J hJ, hc _ _ z J hJ, val_one, val_one, ← Over.comp_left,
    ← Over.comp_left, lift_fst, lift_fst]

theorem commVal_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)} (ht : t.IsGen)
    {k : ℤ} {l : ℕ} {T T' Z : Over S} (χ φ' : ThetaGrp A L (k * l) T) (ψ φ : ThetaGrp A L k T') (s : Z ⟶ T)
    (s' : Z ⟶ T') (hx : s' ≫ ψ.pt = (s ≫ χ.pt) ^ l) (hy : s' ≫ φ.pt = s ≫ φ'.pt) {z : Z.left} {J}
    (hJ : Good L z J) : commVal χ φ' s 1 z J = commVal ψ φ s' 1 z J := by
  have := hA.comm
  obtain ⟨x, hx'⟩ : ∃ x, x = s ≫ χ.pt := ⟨_, rfl⟩
  obtain ⟨y, hy'⟩ : ∃ y, y = s ≫ φ'.pt := ⟨_, rfl⟩
  rw [← hx'] at hx
  rw [← hy'] at hy
  have v₁ : ∀ a b : Z ⟶ A, cubeVal t z J a 1 b = cubeVal t z J a 1 1 := fun a b => by
    simpa using (Rep.cube ht (fst Z A ≫ a) 1 (snd Z A)).rigid hG hA hL (by
      simp only [_root_.mul_one, _root_.one_mul]; abel) b hJ
  have v₂ : ∀ a b : Z ⟶ A, cubeVal t z J a b 1 = cubeVal t z J a 1 1 := fun a b => by
    simpa using (Rep.cube ht (fst Z A ≫ a) (snd Z A) 1).rigid hG hA hL (by
      simp only [_root_.mul_one, _root_.one_mul]; abel) b hJ
  have v₃ : ∀ a b c : Z ⟶ A, cubeVal t z J a b c * (cubeVal t z J a c b)⁻¹ =
      cubeVal t z J a b 1 * (cubeVal t z J a 1 b)⁻¹ := fun a b c => by
    simpa using ((Rep.cube ht (fst Z A ≫ a) (fst Z A ≫ b) (snd Z A)).mul
      (Rep.cube ht (fst Z A ≫ a) (snd Z A) (fst Z A ≫ b)).inv).rigid hG hA hL (by
        rw [mul_right_comm (fst Z A ≫ a) (snd Z A), mul_comm (snd Z A)]; abel) c hJ
  rw [commVal, commVal, ← hx', ← hy', hx, hy, _root_.mul_one, _root_.mul_one, _root_.mul_one]
  refine comm_eq (cubeVal t z J) (fun a => thetaVal φ s' a z J) (fun a => thetaVal φ' s a z J)
    (fun a => thetaVal ψ s' a z J) (fun a => thetaVal χ s a z J) k l x y (fun a => ?_) (fun w => ?_) ?_ ?_
  · have e := v₃ a x y
    rw [v₁ a x, v₂ a x, mul_inv_cancel, mul_inv_eq_one] at e
    rw [e, v₂ a x, v₂ a y]
  · have e := (((((Rep.theta φ (fst Z A ≫ s') ((fst Z A ≫ w) * snd Z A)).mul
      (Rep.theta φ (fst Z A ≫ s') 1)).mul ((Rep.cube ht (fst Z A ≫ w) (fst Z A ≫ y) (snd Z A)).zpow k)).mul
      (Rep.theta φ (fst Z A ≫ s') (fst Z A ≫ w)).inv).mul (Rep.theta φ (fst Z A ≫ s') (snd Z A)).inv).rigid
      hG hA hL (by
        rw [Category.assoc, hy, mul_left_comm (fst Z A ≫ y), _root_.mul_assoc, mul_comm (fst Z A ≫ y) (fst Z A ≫ w),
          _root_.mul_one]
        module) x hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'
  · have e := (((((Rep.theta χ (fst Z A ≫ s) (snd Z A)).mul
      (Rep.theta ψ (fst Z A ≫ s') 1)).mul ((Rep.cubeProd ht (fst Z A ≫ x) (snd Z A) l).zpow k).inv).mul
      (Rep.theta χ (fst Z A ≫ s) 1).inv).mul (Rep.theta ψ (fst Z A ≫ s') (snd Z A)).inv).rigid
      hG hA hL (by
        rw [Category.assoc, Category.assoc, hx, ← hx', MonObj.comp_pow, _root_.mul_one, _root_.mul_one]
        module) y hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'
  · have e := ((((Rep.theta φ' (fst Z A ≫ s) (snd Z A)).mul
      ((Rep.theta φ (fst Z A ≫ s') 1).pow l)).mul
      (Rep.theta φ' (fst Z A ≫ s) 1).inv).mul ((Rep.theta φ (fst Z A ≫ s') (snd Z A)).pow l).inv).rigid
      hG hA hL (by
        rw [Category.assoc, Category.assoc, hy, ← hy']
        module) x hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'

theorem weilIs_value_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)}
    (ht : t.IsGen) {k : ℤ} {l : ℕ} {T : Over S} {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A L (k * l) x y c) (h' : WeilIs A L k (x ^ l) y c') : c = c' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', ⟨θx', θy', hx', hy'⟩, H'⟩ := h' p
  let z : (V ⊓ V').toScheme := ⟨p, hV, hV'⟩
  let s := overLE (inf_le_left : V ⊓ V' ≤ V)
  let s' := overLE (inf_le_right : V ⊓ V' ≤ V')
  choose J hJ using fun χ : (overRes (V ⊓ V')).left ⟶ A.left => exists_chart hL (χ z)
  have e₁ := (commIsOf_iff hL _ _ _).1 (H θx θy hx hy) _ s 1 z J hJ
  have e₂ := (commIsOf_iff hL _ _ _).1 (H' θx' θy' hx' hy') _ s' 1 z J hJ
  have e₃ := commVal_eq hG hA hL ht θx θy θx' θy' s s'
    (by rw [hx, hx', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι, MonObj.comp_pow])
    (by rw [hy, hy', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι]) (z := z) hJ
  have f₁ := gm_unitRes V c (T.left.homOfLE (inf_le_left : V ⊓ V' ≤ V)) z
  have f₂ := gm_unitRes V' c' (T.left.homOfLE (inf_le_right : V ⊓ V' ≤ V')) z
  rw [Scheme.homOfLE_ι] at f₁ f₂
  exact gm_inj (V ⊓ V').ι z (U := ⊤) (U' := ⊤) trivial trivial (f₁.symm.trans (e₁.symm.trans (e₃.trans (e₂.trans f₂))))

theorem weilIs_mul_iff : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) → x ^ (k * l) = 1 → y ^ k = 1 → (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c) := by
  intro hG hT _ hW S P k T l x y c _ hx hy
  obtain ⟨t, ht⟩ := hT S P P.L P.isLB
  obtain ⟨c₁, h₁, -⟩ := hW S P (k * l) T x y hx (by rw [pow_mul, hy, one_pow])
  obtain ⟨c₂, h₂, -⟩ := hW S P k T (x ^ l) y (by rw [← pow_mul, mul_comm, hx]) hy
  rw [Nat.cast_mul] at h₁
  constructor
  · intro h
    rw [weilIs_value_eq hG P.isAb P.isLB ht h h₂]; exact h₂
  · intro h
    rw [← weilIs_value_eq hG P.isAb P.isLB ht h₁ h]; exact h₁

end GlobalTheory.PairingLevels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescentPairing

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem interchange (p q r s x : A) :
    θ (p * q) (r * s) x * θ p q x * θ r s x = θ (p * r) (q * s) x * θ p r x * θ q s x := by
  have a := h.coc p q (r * s) x
  have b := h.coc q r s x
  have c := h.coc r q s x
  have d := h.coc p r (q * s) x
  rw [mul_comm r q, h.s01 r q] at c
  rw [mul_left_comm r q s] at d
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a' := E a; have b' := E b; have c' := E c; have d' := E d
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a' - b' + c' - d'

theorem cubN_mul (k : ℕ) (a b x : A) :
    cubN θ k 1 (a * b) x * θ a b x ^ k = θ (a ^ k) (b ^ k) x * cubN θ k 1 a x * cubN θ k 1 b x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := interchange h (a ^ k) (b ^ k) a b x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ a, pow_succ b, pow_succ (θ a b x), mul_pow a b k]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem cubN_transl (k : ℕ) (y w x : A) (hy : y ^ k = 1) :
    cubN θ k 1 (y * w) x * cubN θ k 1 y w = cubN θ k 1 w x * cubN θ k 1 y (x * w) := by
  have a := cubN_mul h k y w x
  have b := h.N_add k 1 y x w
  rw [hy, h.face, _root_.one_mul] at a
  rw [hy, _root_.mul_one (1 : A), h.face, _root_.one_mul, _root_.mul_one, h.s12 y x w] at b
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a' b' ⊢
  linear_combination (norm := abel) a' - b'

end Alg

theorem exists_frame {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y₀ : Y) (hY : ∀ y : Y, y = y₀) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y₀)
  have m₀ : ∀ y : Y, y ∈ LB.wchart M φ (fun k => I (φ k)) := fun y => by
    rw [hY y]; exact Set.mem_iInter.2 fun k => hI _
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ (fun k => I (φ k)) := fun j y hy => ⟨hy, m₀ y⟩
  have v : ∀ j (y : Y), y ∈ LB.wchart M φ j →
      gm (𝟙 Y) y _ (res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))) = trF φ ε (𝟙 Y) y j (fun k => I (φ k)) :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb M φ ε (𝟙 Y) y j _ hy (m₀ y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)
  exact trF_trans hM φ ε (𝟙 Y) y hy.1 hy.2 (m₀ y)

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem exists_theta {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ A) (hy : y ^ n = 1) :
    ∃ θ : ThetaGrp A L.L n T, θ.pt = y ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, thetaVal θ t a z J = cubN (cubV c z J) n 1 (t ≫ y) a * s := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(n : ℤ), -n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ y) (snd T A) n
  have e₁ : (fst T A ≫ y) ^ n = 1 :=
    (map_pow (preHom (fst T A)) y n).symm.trans (by rw [hy]; exact map_one _)
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A y).left])
    (ε' := ![(n : ℤ), -n]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A y = (fst T A ≫ y) * snd T A := rfl
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.pullGen L.L _ _ σ (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨⟨y, u, hu⟩, rfl, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_triv {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (θ : ThetaGrp A L.L n T) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, val u (lift t a).left z J =
        cubN (cubV c z J) n 1 a (t ≫ θ.pt) * ((thetaVal θ t a z J)⁻¹ * s) := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, θ.pt.left] ![(n : ℤ) - 1, 1 - n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (snd T A) (fst T A ≫ θ.pt) n
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2)
    (φ' := ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left]) (ε' := ![1, -1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : mulT A T n ≫ translPt A θ.pt = snd T A ^ n * (fst T A ≫ θ.pt) :=
        (lift_translPt θ.pt _ _).trans (mul_comm _ _)
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A θ.pt = snd T A * (fst T A ≫ θ.pt) := mul_comm (fst T A ≫ θ.pt) (snd T A)
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![(n : ℤ), -n] θ.φ)
      (LB.pullGen L.L _ _ σ (fst T A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ.isGen)
      (DVR.pullGen_isGen _ _ _ _ hσ _)))
  refine ⟨u, hu, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_pull hJ _ _ _).trans ?_)))))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_gen_transl_eq_pairing : GlobalFnsSt → CubeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → WeilSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε))) := by
  intro _ hC hW _ K _ _ P n x hx
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let p₀ : (baseOver (Spec (CommRingCat.of K))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hT : ∀ p : (baseOver (Spec (CommRingCat.of K))).left, p = p₀ := fun p =>
    Subsingleton.elim (α := PrimeSpectrum K) p p₀
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, 1, hu, Or.inl rfl, fun y c hy hc => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff P.isLB θx θy c).1 (((hW _ P n _).1 θx θy c).1 hc)
  refine corr_of_val P.isLB fun z J hJ => ?_
  have e : 𝟙 (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left = (lift (fst _ P.A) (snd _ P.A)).left := by
    rw [lift_fst_snd]; rfl
  rw [e]
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg (_ * ·) (val_const (c ^ (1 : ℤ)) _ _ z J))).symm)
  rw [← Over.comp_left, lift_translT, zpow_one]
  obtain ⟨s, hs⟩ := vu _ (fst _ P.A) z J hJ
  obtain ⟨s', hs'⟩ := vy _ (fst _ P.A) z J hJ
  have k₁ := hcm _ (fst _ P.A) (snd _ P.A) z J hJ
  have C : IsCub (cubV cb z J) := by
    as_aux_lemma =>
      refine {
        face x y := by
          have := val_corr hJ (cb.face 0) (lift x y).left
          rw [val_one] at this
          refine Eq.trans ?_ this
          refine Eq.trans ?_ (val_cub cb (lift x y) hJ (pzero P.A _) (x2 P.A 0) (x2 P.A 1)).symm
          congr 1 <;> simp [x2, pzero, Hom.one_def]
        s01 x y w := by
          have := (val_corr hJ cb.cubeSymmetric_swap_first (lift x (lift y w)).left).trans (val_cub cb (lift x (lift y w)) hJ _ _ _)
          refine Eq.trans this ?_
          congr 1 <;> simp [x3]
        s12 x y w := by
          have := (val_corr hJ cb.cubeSymmetric_swap_last (lift x (lift y w)).left).trans (val_cub cb (lift x (lift y w)) hJ _ _ _)
          refine Eq.trans this ?_
          congr 1 <;> simp [x3]
        coc x x' x'' y := by
          have := val_corr hJ cb.cocycle (lift x (lift x' (lift x'' y))).left
          have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb _ hJ _ _ _) (val_cub cb _ hJ _ _ _))).symm.trans
            (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb _ hJ _ _ _) (val_cub cb _ hJ _ _ _))))
          have a₀ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 0 = x := by simp [x4]
          have a₁ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 1 = x' := by simp [x4]
          have a₂ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 2 = x'' := by simp [x4]
          have a₃ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 3 = y := by simp [x4]
          have b₀ : lift x (lift x' (lift x'' y)) ≫ padd P.A (x4 P.A 0) (x4 P.A 1) = x * x' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
          have b₁ : lift x (lift x' (lift x'' y)) ≫ padd P.A (x4 P.A 1) (x4 P.A 2) = x' * x'' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
          rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
      }
  have k₂ := cubN_transl C n (fst _ P.A ≫ θy.pt) (snd _ P.A) (fst _ P.A ≫ θx.pt)
    ((map_pow (preHom (fst _ P.A)) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' (snd _ P.A)
  have t₂ := hs' ((fst _ P.A ≫ θx.pt) * snd _ P.A)
  apply Additive.ofMul.injective
  have E := fun {p q : ((baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left.presheaf.stalk z)ˣ} (e : p = q) =>
    congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end GlobalTheory.DescentPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EndDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

def germPull {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) :
    Γ(Y, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem germPull_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    germPull r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_appLE {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : f z ∈ V) (a : Γ(X, U)) :
    gs f z V ((r.appLE U V hle).hom a) = gs (f ≫ r) z U a :=
  (gs_res f z hle h _).trans (gs_pull f r z U (hle h) a)

theorem exists_factor {X W Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated] [IsAffine S] (f : X ⟶ W)
    (w : W ⟶ Y) (g : X ⟶ S) (hS : IsField Γ(S, ⊤)) (D : W.Opens) (hD : IsAffineOpen D) (z : X) (hz : f z ∈ D)
    (h : ∀ a : Γ(W, D), ∃ c : Γ(S, ⊤), gs g z ⊤ c = gs f z D a) : ∃ p : S ⟶ Y, f ≫ w = g ≫ p := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVD⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ ((f ⁻¹ᵁ D : X.Opens) : Set X) from hz)
      (f ⁻¹ᵁ D).isOpen
  have hVD' : V ≤ f ⁻¹ᵁ D := hVD
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  let κ := (g.appLE ⊤ V le_top).hom
  let φ := (f.appLE D V hVD').hom
  have hκ : Function.Injective κ := by
    letI := hS.toField
    exact κ.injective
  have hr : ∀ a, φ a ∈ κ.range := fun a => by
    obtain ⟨c, hc⟩ := h a
    refine ⟨c, germ_injective_of_isIntegral X z hzV ?_⟩
    refine (gs_eq (𝟙 X) z V hzV _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X) z V hzV _))
    refine (gs_appLE (𝟙 X) g z ⊤ V le_top hzV c).trans
      (Eq.trans ?_ (gs_appLE (𝟙 X) f z D V hVD' hzV a).symm)
    rw [Category.id_comp, Category.id_comp, hc]
  let e : Γ(S, ⊤) ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b hab => hκ (congrArg Subtype.val hab), κ.rangeRestrict_surjective⟩
  let χ : Γ(W, D) ⟶ Γ(S, ⊤) := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict κ.range hr))
  have hχ : f.appLE D V hVD' = χ ≫ g.appLE ⊤ V le_top := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hr a⟩)).symm
  refine ⟨S.isoSpec.hom ≫ Spec.map χ ≫ hD.fromSpec ≫ w, ?_⟩
  have : IsDominant hV.fromSpec := ⟨by
    rw [DenseRange, hV.range_fromSpec]
    exact V.isOpen.dense ⟨z, hzV⟩⟩
  refine ext_of_isDominant hV.fromSpec ?_
  rw [← Category.assoc, ← hD.SpecMap_appLE_fromSpec f hV hVD', ← Category.assoc hV.fromSpec,
    ← (isAffineOpen_top S).SpecMap_appLE_fromSpec g hV le_top, hχ, IsAffineOpen.fromSpec_top]
  simp

theorem exists_monomials {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (t : ℕ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(t : ℤ), -1])) (hα : α.IsGen)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w ≫ m) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    ∃ b : (Z.presheaf.stalk z)ˣ, ∀ a ≤ t,
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => (N : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) * b.val := by
  obtain ⟨β, hβ⟩ : ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k)
      (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)), β.IsGen :=
    exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hα (f ≫ w)) _
  refine ⟨val β (𝟙 Z) z J, fun a ha => ?_⟩
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N ⊕ Fin 2)
      (Sum.elim (fun _ => f ≫ w) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k))
      (Sum.elim (fun _ => 1) (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)) (fun _ : Unit => u) (fun _ => (N : ℤ)) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, hu]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      Category.assoc, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha]
    rw [← _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
    simp [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullMulSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f β hβ)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem mem_range_of_sum_eq_zero {K R : Type} [Field K] [IsAlgClosed K] [CommRing R] [IsDomain R]
    (κ : K →+* R) {n : ℕ} (c : Fin n → K) (hc : c ≠ 0) (x : R) (h : ∑ k, κ (c k) * x ^ (k : ℕ) = 0) :
    x ∈ κ.range := by
  let p : Polynomial K := ∑ k : Fin n, Polynomial.monomial (k : ℕ) (c k)
  have hp : p ≠ 0 := fun h0 => hc (funext fun k => by
    have := congrArg (fun q : Polynomial K => q.coeff k) h0
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Polynomial.coeff_zero] at this
    exact this)
  refine (IsAlgClosed.splits p).mem_range_of_isRoot hp ?_
  rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finsetSum]
  simpa [Polynomial.eval₂_monomial] using h

theorem eq_one_of_forall_pow_dvd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1 := by
  intro hGI hmul hfin K _ _ P q hq u hu
  have := P.isAb.proper
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]; infer_instance⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, -, M, s, hcov, hs⟩ := P.ample ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := hfin K P _ (DVR.linComb_isLB P.L P.isLB (K := Unit) (fun _ => u.left) (fun _ => (N : ℤ)))
  obtain ⟨ψ, hψ, hu⟩ := hu n
  have H := hmul _ P (q ^ n)
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have hnt : n ≤ (q ^ n) ^ 2 := (Nat.lt_pow_self hq).le.trans (Nat.le_self_pow two_ne_zero _)
  let w := (P.A.hom ⁻¹ᵁ ⊤).ι
  let f : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hu' : u.left = f ≫ w ≫ (mulA P.A (q ^ n)).left := by
    rw [← Category.assoc, hf, ← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, hu]
  obtain ⟨z⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good P.L z J := by
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ z)
    exact ⟨I, hI⟩
  let κ := germPull P.A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver P.A P.L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    obtain ⟨b, hb⟩ := exists_monomials P.L P.isLB w N (s i) (s j) _ _ α hα f u.left hu' z J hJ
    choose σ hσ using fun a : Fin n => hb a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn σ
    have hm := hJ.mem (K := Unit) (fun _ => u.left) (𝟙 _)
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (fun _ => J (𝟙 _ ≫ u.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (E (c k)) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ ((q ^ n) ^ 2) * b.val) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) P.A.hom z ⊤ _ le_top hm (c k)) (hσ k)).symm
      have e₁ : (κ.comp E.symm.toRingHom) (E (c k)) = gs (𝟙 _ ≫ P.A.hom) z ⊤ (c k) := by
        rw [Category.id_comp]
        exact (congrArg κ (E.symm_apply_apply _)).trans (germPull_apply _ _ _ _ _)
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) (fun k => E (c k))
      (fun h => hc (funext fun k => E.injective ((congrFun h k).trans (map_zero E).symm))) (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right ((hy.pow _).mul b.isUnit).ne_zero)
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w P.A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have h2 : η[P.A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  have h3 : ψ = 1 := by
    apply Over.OverMorphism.ext
    rw [hp, ← h2, Hom.one_def]
    simp
  rw [hu, h3, one_pow]

end GlobalTheory.EndDivisible
end
end

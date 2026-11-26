module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLe
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolyNormSqRoots
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolyNormSqRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroupStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem card_torsion_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  intro k _ _ B _ hB L _ a ha
  refine ⟨1, fun n hn => ?_⟩
  have h := GlobalTheory.T.abelianVarietyTorsionCardEqPow k B a n hB ha hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact pow_ne_zero _ hn0
  · rw [h, Nat.one_mul]

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_abelianVariety_le_const_mul_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  first | exact @GlobalTheory.SS.card_torsion_le | exact GlobalTheory.SS.card_torsion_le | (intros; apply GlobalTheory.SS.card_torsion_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPowOfFix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

theorem gen_of_cover {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} (V : A → Y.Opens) (J : A → K → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ LB.wchart L φ (J a))
    (h1 : ∀ a b y, y ∈ V a → y ∈ V b → trF φ ε (𝟙 Y) y (J a) (J b) = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have glue : ∀ j : K → L.ι, ∃ s : Γ(Y, LB.wchart L φ j)ˣ, ∀ a y, y ∈ LB.wchart L φ j → y ∈ V a →
      gm (𝟙 Y) y _ s = trF φ ε (𝟙 Y) y j (J a) := by
    intro j
    have le : ∀ a, LB.wchart L φ j ⊓ V a ≤ LB.wchart L φ j ⊓ LB.wchart L φ (J a) :=
      fun a => inf_le_inf_left _ (hV a)
    have hu : ∀ a y, y ∈ LB.wchart L φ j ⊓ V a →
        gm (𝟙 Y) y _ (res (le a) ((LB.LinComb L φ ε).g j (J a))) = trF φ ε (𝟙 Y) y j (J a) := fun a y hy =>
      (gm_res (𝟙 Y) y (le a) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j (J a) hy.1 (hV a hy.2))
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ j) (fun a => LB.wchart L φ j ⊓ V a) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨a, ha⟩ := hc y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy, ha⟩)
      (fun a => res (le a) ((LB.LinComb L φ ε).g j (J a))) (fun a b y hy => by
        refine (hu a y hy.1).trans (Eq.trans ?_ (hu b y hy.2).symm)
        rw [← trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hV a hy.1.2) (hV b hy.2.2), h1 a b y hy.1.2 hy.2.2, _root_.mul_one])
    refine ⟨s, fun a y h₁ h₂ => ?_⟩
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j ⊓ V a := ⟨h₁, h₂⟩
    exact (gm_res (𝟙 Y) y inf_le_left hm s).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs a)).trans (hu a y hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  refine ((gm_res (𝟙 Y) y _ hy _).trans (hs j a y hy.1 ha)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (hs j' a y hy.2 ha))).trans ?_)
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hV a ha)

def Fix {X : Scheme.{0}} (φ : X ⟶ X) (U : X.Opens) (f : Γ(X, U)) (n : ℕ) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

theorem Fix.id {X : Scheme.{0}} (U : X.Opens) (f : Γ(X, U)) : Fix (𝟙 X) U f 1 := by
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.appLE]
  exact rs_self (X := X) le_rfl f

theorem Fix.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)} {a b : ℕ}
    (h : Fix φ U f a) (h' : Fix ψ U f b) : Fix (φ ≫ ψ) U f (a * b) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨e', h'⟩ := h'
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e', ← e], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e'.le e.le, CommRingCat.hom_comp, RingHom.comp_apply, h', map_pow, h,
    pow_mul]

theorem Fix.pow {S : Scheme.{0}} {G : Over S} {F : End G} {U : G.left.Opens} {f : Γ(G.left, U)} {q m : ℕ}
    (h : Fix (F ^ m).asHom.left U f (q ^ m)) (l : ℕ) :
    Fix (F ^ (m * l)).asHom.left U f (q ^ (m * l)) := by
  induction l with
  | zero => exact Fix.id U f
  | succ l ih =>
    rw [mul_add, Nat.mul_one, pow_add, pow_add, mul_comm (q ^ _)]
    exact h.comp ih

theorem Fix.gm {X : Scheme.{0}} {φ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {n : ℕ} (h : Fix φ U f.val n)
    (x : X) (hx : x ∈ U) : gm φ x U f = gm (𝟙 X) x U f ^ n := by
  obtain ⟨e, h⟩ := h
  have hx' : φ x ∈ U := e.le hx
  have h2 : res e.le (pullU φ U f) = f ^ n := Units.ext h
  rw [← map_pow, ← h2, gm_res (𝟙 X) x e.le hx, gm_pull (𝟙 X) φ x U hx', Category.id_comp]

theorem pullPow_of_fix {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : X ⟶ X) (n : ℕ)
    {A : Type} (V : A → X.Opens) (c : A → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ L.U (c a))
    (h : ∀ a b, Fix φ (V a ⊓ V b) (res (inf_le_inf (hV a) (hV b)) (L.g (c a) (c b))).val n) :
    PullPow φ L n := by
  refine gen_of_cover hL _ _ V (fun a _ => c a) hc (fun a y hy => Set.mem_iInter.2 fun k => ?_) fun a b y ha hb => ?_
  · fin_cases k
    · exact hV a ((h a a).1.le ⟨hy, hy⟩).1
    · exact hV a hy
  · have hm : y ∈ V a ⊓ V b := ⟨ha, hb⟩
    have e := (h a b).gm y hm
    have hm' : φ y ∈ V a ⊓ V b := (show V a ⊓ V b ≤ φ ⁻¹ᵁ (V a ⊓ V b) from (h a b).1.le) hm
    rw [gm_res φ y _ hm', gm_res (𝟙 X) y _ hm] at e
    simp only [trF, Fin.prod_univ_two, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, e]
    simp

theorem frob_pullPow : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (F : End G) (q : ℕ), FrobG G F q → ∀ L : LB G.left, L.IsLB → ∃ m, 1 ≤ m ∧ ∀ l, PullPow (F ^ (m * l)).asHom.left L ((q : ℤ) ^ (m * l)) := by
  intro k _ G _ hG F q hF L hL
  classical
  obtain ⟨-, -, hsep, hqc, -⟩ := hG
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hx : ∀ x : G.left, ∃ (V : G.left.Opens) (i : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, h₁, h₂⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hi (L.U i).isOpen
    exact ⟨V, i, hV, h₁, h₂⟩
  choose V c hA hxV hV using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set G.left)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  choose m hm hfix using fun p : s × s => hF.2 (V p.1 ⊓ V p.2) ((hA p.1).inf (hA p.2))
    (res (inf_le_inf (hV p.1) (hV p.2)) (L.g (c p.1) (c p.2))).val
  refine ⟨∏ p, m p, Finset.one_le_prod' fun p _ => hm p, fun l => ?_⟩
  have := pullPow_of_fix hL (F ^ ((∏ p, m p) * l)).asHom.left (q ^ ((∏ p, m p) * l))
    (fun a : s => V a) (fun a => c a) (fun y => by
      obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact ⟨⟨a, ha⟩, hy⟩) (fun a => hV a) (fun a b => by
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (a, b))
      rw [hr, Nat.mul_assoc]
      exact Fix.pow (hfix (a, b)) _)
  exact_mod_cast this

end GlobalTheory.SS.FrobLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGSplitTorusPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem appTop_pow_mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) (f : Γ(G.left, ⊤))
    (h : (F ^ m).asHom.left.appTop.hom f = f ^ (q ^ m)) (j : ℕ) :
    (F ^ (m * j)).asHom.left.appTop.hom f = f ^ (q ^ (m * j)) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, pow_one]
    change (Scheme.Hom.appTop (𝟙 G.left)).hom f = f
    simp
  | succ j ih =>
    have e : (F ^ (m * (j + 1))).asHom.left =
        (F ^ m).asHom.left ≫ (F ^ (m * j)).asHom.left := by
      rw [Nat.mul_succ, pow_add]; rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h,
      ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]

theorem isAffine_splitTorus (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Sp k) X).left := by
  have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Spec ZU.{0}) := inferInstance
  exact inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))

theorem frobG_splitTorus_pow :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q →
        ∃ m, 1 ≤ m ∧ ∀ l, (F ^ (m * l)).asHom = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by
  intro k _ X _ _ _ F q hF
  classical
  have := isAffine_splitTorus k X
  have key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧
      (F ^ m).asHom.left.appTop.hom
        (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m) := by
    intro χ
    obtain ⟨m, hm, h, hh⟩ := hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val
    refine ⟨m, hm, ?_⟩
    rw [← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  choose n0 hn1 hn using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩
  let e := splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)
  apply e.injective
  rw [map_pow]
  have hgen : ∀ χ ∈ s, e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom (Multiplicative.ofAdd χ) =
      (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ) := by
    intro χ hχ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n0 hχ
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val,
      splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]
    congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x.toAdd ∈ Submodule.span ℤ (s : Set X) := by rw [hs]; trivial
  generalize e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom = a at hgen ⊢
  generalize (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢
  change a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)
  generalize x.toAdd = w at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]
  | smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGPowAndClosedSubgroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.FrobSub

def Raises {X : Scheme.{0}} (φ : X ⟶ X) (n : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

theorem Raises.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {a b : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (h₁ : Raises φ a U f) (h₂ : Raises ψ b U f) : Raises (φ ≫ ψ) (a * b) U f := by
  obtain ⟨e₁, p₁⟩ := h₁
  obtain ⟨e₂, p₂⟩ := h₂
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e₂, ← e₁], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e₂.le e₁.le, CommRingCat.hom_comp, RingHom.comp_apply, p₂,
    map_pow, p₁, ← pow_mul]

theorem Raises.mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) {U : G.left.Opens} {f : Γ(G.left, U)}
    (h : Raises (F ^ m).asHom.left (q ^ m) U f) (n : ℕ) (hn : 1 ≤ n) :
    Raises (F ^ (m * n)).asHom.left (q ^ (m * n)) U f := by
  induction n, hn using Nat.le_induction with
  | base => rwa [Nat.mul_one]
  | succ n hn ih =>
    have := h.comp ih
    rw [Nat.mul_succ, pow_add, End.mul_asHom, pow_add, mul_comm (q ^ (m * n))]
    exact this

theorem Raises.pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {φ : X ⟶ X} {ψ : Y ⟶ Y} (hc : ψ ≫ ν = ν ≫ φ) {a : ℕ}
    {V : X.Opens} {g : Γ(X, V)} (h : Raises φ a V g) : Raises ψ a (ν ⁻¹ᵁ V) ((ν.app V).hom g) := by
  obtain ⟨e, p⟩ := h
  have e' : ν ⁻¹ᵁ V = ψ ⁻¹ᵁ ν ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, ← e]
  refine ⟨e', ?_⟩
  have k : ∀ (θ θ' : Y ⟶ X) (_ : θ = θ') h h', θ.appLE V (ν ⁻¹ᵁ V) h = θ'.appLE V (ν ⁻¹ᵁ V) h' := by
    rintro _ _ rfl _ _; rfl
  have k2 : ν.appLE V (ν ⁻¹ᵁ V) le_rfl ≫ ψ.appLE _ _ e'.le =
      φ.appLE V V e.le ≫ ν.appLE V (ν ⁻¹ᵁ V) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact k _ _ hc _ _
  rw [Scheme.Hom.app_eq_appLE]
  have := congrArg (fun t => t.hom g) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, p, map_pow]

theorem Raises.of_cover {X : Scheme.{0}} {φ : X ⟶ X} {a : ℕ} {U : X.Opens} {f : Γ(X, U)} {I : Type}
    (V : I → X.Opens) (hV : ∀ i, V i ≤ U) (hU : U ≤ iSup V)
    (h : ∀ i, Raises φ a (V i) ((X.presheaf.map (homOfLE (hV i)).op).hom f)) : Raises φ a U f := by
  have hU' : U = iSup V := le_antisymm hU (iSup_le hV)
  have e : U = φ ⁻¹ᵁ U := by
    rw [hU', Scheme.Hom.preimage_iSup]
    exact iSup_congr fun i => (h i).1
  refine ⟨e, ?_⟩
  refine X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hU _ _ fun i => ?_
  obtain ⟨e', p⟩ := h i
  have k2 : φ.appLE U U e.le ≫ X.presheaf.map (homOfLE (hV i)).op =
      X.presheaf.map (homOfLE (hV i)).op ≫ φ.appLE _ _ e'.le := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have := congrArg (fun t => t.hom f) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans (p.trans (map_pow _ _ _).symm)

theorem pow_comm_hom {C : Type*} [Category C] {N G : C} (ν : N ⟶ G) (F : End G) (F' : End N)
    (h : F'.asHom ≫ ν = ν ≫ F.asHom) (m : ℕ) :
    (F' ^ m).asHom ≫ ν = ν ≫ (F ^ m).asHom := by
  induction m with
  | zero => simp [End.one_asHom]
  | succ m ih =>
    simp only [pow_succ, End.mul_asHom, Category.assoc] at *
    rw [ih, reassoc_of% h]

theorem isMonHom_pow {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G)
    (h : IsMonHom F.asHom) (m : ℕ) : IsMonHom (F ^ m).asHom := by
  induction m with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 G))
  | succ m ih =>
    rw [pow_succ, End.mul_asHom]
    infer_instance

end GlobalTheory.SS.FrobSub


open GlobalTheory.SS.FrobSub in
theorem GlobalTheory.SS.frobG_pow_and_closed_subgroup :
    ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G →
      ∀ (F : End G) (q : ℕ), FrobG G F q →
        (∀ m, 1 ≤ m → FrobG G (F ^ m) (q ^ m)) ∧
        ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (F' : End N),
          IsMonHom ν → IsClosedImmersion ν.left → IsMonHom F'.asHom →
          F'.asHom ≫ ν = ν ≫ F.asHom → FrobG N F' q := by
  intro k _ G _ _ F q hF
  refine ⟨fun m hm => ⟨isMonHom_pow G F hF.1 m, fun U hU f => ?_⟩, fun N _ ν F' _ hν hF' hc => ⟨hF', fun U hU f => ?_⟩⟩
  · obtain ⟨n, hn, h⟩ := hF.2 U hU f
    refine ⟨n, hn, ?_⟩
    have := Raises.mul F q n h m hm
    rw [mul_comm, pow_mul, pow_mul] at this
    exact this
  · have key : ∀ x : U, ∃ (W : N.left.Opens) (hW : W ≤ U) (m : ℕ), x.1 ∈ W ∧ 1 ≤ m ∧
        Raises (F' ^ m).asHom.left (q ^ m) W ((N.left.presheaf.map (homOfLE hW).op).hom f) := by
      intro x
      obtain ⟨W, hW, hWU⟩ := ν.left.isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
      have hx : ν.left x.1 ∈ (⟨W, hW⟩ : G.left.Opens) := by
        show x.1 ∈ ν.left ⁻¹' W
        rw [hWU]; exact x.2
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
      have hle : ν.left ⁻¹ᵁ V ≤ U := fun y hy => by
        have : y ∈ ν.left ⁻¹' W := hVW hy
        rwa [hWU] at this
      obtain ⟨g, hg⟩ := ν.left.app_surjective V hV ((N.left.presheaf.map (homOfLE hle).op).hom f)
      obtain ⟨m, hm, h⟩ := hF.2 V hV g
      refine ⟨_, hle, m, hxV, hm, ?_⟩
      rw [← hg]
      refine Raises.pull ν.left ?_ h
      exact congrArg (fun t => t.left) (pow_comm_hom ν F F' hc m)
    choose W hW m hxW hm hR using key
    obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun x => (W x : Set N.left)) (fun x => (W x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩)
    have hpos : 1 ≤ ∏ x ∈ t, m x := Finset.one_le_prod fun x _ => hm x
    refine ⟨∏ x ∈ t, m x, hpos, ?_⟩
    refine Raises.of_cover (fun x : t => W x.1) (fun x => hW x.1) (fun y hy => ?_) fun x => ?_
    · obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy'⟩
    · obtain ⟨n, hn⟩ := Finset.dvd_prod_of_mem m x.2
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => by rw [hn, h0] at hpos; simp at hpos
      rw [hn]
      exact Raises.mul F' q _ (hR x.1) n hn1
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.FrobTorsion

theorem card_torsion_le_mul {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B) (n : ℕ)
    [Finite {x : A // f x = 1 ∧ x ^ n = 1}] [Finite {y : B // y ^ n = 1}] :
    Finite {x : A // x ^ n = 1} ∧
      Nat.card {x : A // x ^ n = 1} ≤ Nat.card {x : A // f x = 1 ∧ x ^ n = 1} * Nat.card {y : B // y ^ n = 1} := by
  classical
  let c : B → A := fun b => if h : ∃ a : {x : A // x ^ n = 1}, f a = b then (h.choose : A) else 1
  have hc : ∀ x : {x : A // x ^ n = 1}, (c (f x)) ^ n = 1 ∧ f (c (f x)) = f x := by
    intro x
    have h : ∃ a : {x : A // x ^ n = 1}, f a = f x := ⟨x, rfl⟩
    simp only [c, dif_pos h]
    exact ⟨h.choose.2, h.choose_spec⟩
  let Φ : {x : A // x ^ n = 1} → {x : A // f x = 1 ∧ x ^ n = 1} × {y : B // y ^ n = 1} := fun x =>
    (⟨x * (c (f x))⁻¹, by
        refine ⟨?_, ?_⟩
        · rw [map_mul, map_inv, (hc x).2, mul_inv_cancel]
        · rw [mul_pow, inv_pow, x.2, (hc x).1]
          simp⟩,
     ⟨f x, by rw [← map_pow, x.2, map_one]⟩)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    rw [h2] at h1
    exact Subtype.ext (mul_right_cancel h1)
  have : Finite {x : A // x ^ n = 1} := Finite.of_injective Φ hΦ
  refine ⟨inferInstance, ?_⟩
  have := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod] at this

variable {S : Scheme.{0}}

theorem pow_comp' {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem list_prod_comp_degeneration {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (l : List (Z ⟶ G)) : l.prod ≫ φ = (l.map (· ≫ φ)).prod := by
  induction l with
  | nil => simp [MonObj.one_comp]
  | cons a l ih => rw [List.prod_cons, MonObj.mul_comp, ih, List.map_cons, List.prod_cons]

theorem polyPt_comp {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] (E : End G) (F : End H)
    (h : E.asHom ≫ φ = φ ≫ F.asHom) (P : Polynomial ℤ) (x : Z ⟶ G) :
    polyPt E P x ≫ φ = polyPt F P (x ≫ φ) := by
  unfold polyPt
  rw [list_prod_comp_degeneration, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [Function.comp_apply]
  rw [GrpObj.zpow_comp, Category.assoc, GlobalTheory.SS.FrobSub.pow_comm_hom φ F E h n]
  simp only [Category.assoc]

theorem pullPow_pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {F : X ⟶ X} {E : Y ⟶ Y} (h : E ≫ ν = ν ≫ F) {L : LB X} {Q : ℤ}
    (hL : PullPow F L Q) : PullPow E (L.pull ν) Q := by
  obtain ⟨t, ht⟩ := hL
  have hc : ∀ k : Fin 2, ν ≫ (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) k = ((![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) ≫ ν := by
    intro k
    fin_cases k
    · simp [h]
    · simp
  have hle : ∀ (j : Fin 2 → PUnit.{1} → L.ι) (y : Y), y ∈ (L.pull ν).wchart (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) j →
      ν y ∈ L.wchart (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) (fun k => j k PUnit.unit) := by
    intro j y hy
    refine Set.mem_iInter.2 fun k => ?_
    have h2 : ν ((![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k y) ∈ L.U (j k PUnit.unit) := mem_pull.1 (Set.mem_iInter.1 hy k)
    have h3 := congrArg (fun m : Y ⟶ X => m y) (hc k)
    simp only at h3
    change (ν ≫ (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) k) y ∈ L.U (j k PUnit.unit)
    rw [h3]
    exact h2
  let a : ChartPull (LB.LinComb (L.pull ν) (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) ![1, -Q])
      (LB.LinComb L (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) ![1, -Q]) ν :=
    { idx := fun j k => j k PUnit.unit
      le := fun j y hy => hle j y hy
      g := fun y j j' hj hj' => by
        refine (gm_linComb (L.pull ν) _ _ (𝟙 Y) y j j' hj hj').trans
          (Eq.trans ?_ (gm_linComb L _ _ ν y _ _ (hle j y hj) (hle j' y hj')).symm)
        refine Finset.prod_congr rfl fun k _ => ?_
        have m1 : (𝟙 Y ≫ (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) y ∈ (L.pull ν).U (j k) := Set.mem_iInter.1 hj k
        have m2 : (𝟙 Y ≫ (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) y ∈ (L.pull ν).U (j' k) := Set.mem_iInter.1 hj' k
        rw [gm_pull_g L ν _ y (j k) (j' k) m1 m2, Category.id_comp, ← hc k] }
  obtain ⟨u, hu⟩ := gen_chartPull a t ht
  exact ⟨u, hu⟩

private theorem isMonHom_mul_degeneration {S : Scheme.{0}} {M G : Over S} [MonObj M] [GrpObj G] [IsCommMonObj G]
    (f g : M ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem isMonHom_id_pow (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero =>
    rw [pow_zero, Hom.one_def]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    exact isMonHom_mul_degeneration _ _

theorem norm_lt_of_normSq {β : ℂ} {Q : ℕ} (hQ : 2 ≤ Q) (h : Complex.normSq β = Q) : ‖β‖ < Q := by
  have h1 : ‖β‖ ^ 2 = (Q : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, h]
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : 0 ≤ ‖β‖ := norm_nonneg β
  nlinarith

private theorem comp_mul_inv_pow_eq_one_iff {S : Scheme.{0}} {N Z : Over S} [GrpObj N] [IsCommMonObj N] (E : N ⟶ N) (Q : ℕ)
    (x : Z ⟶ N) : x ≫ (E * ((𝟙 N) ^ Q)⁻¹) = 1 ↔ x ≫ E = x ^ Q := by
  rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, Category.comp_id, mul_inv_eq_one]

private theorem inv_mul_mul_mul_eq_mul {S : Scheme.{0}} {N : Over S} [GrpObj N] [IsCommMonObj N] (E : N ⟶ N) [IsMonHom E] (Q : ℕ) :
    E ≫ (E * ((𝟙 N) ^ Q)⁻¹) = (E * ((𝟙 N) ^ Q)⁻¹) ≫ E := by
  rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, Category.comp_id, MonObj.mul_comp, GrpObj.inv_comp,
    MonObj.pow_comp, Category.id_comp]

theorem core (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N] (hN : SmConn N)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B]
    (i : splitTorus (Sp k) X ⟶ N) (q : N ⟶ B) (hq : IsQuot i q) (hB : IsAbelianScheme B)
    (L : LB N.left) (hL : AmpleCub N L) (E : N ⟶ N) [IsMonHom E] (Q : ℕ) (hQ : 2 ≤ Q)
    (hE : PullPow E.left L Q) (hi : i ≫ E = i ^ Q) (a : ℕ) (ha : SmoothOfRelativeDimension a B.hom) :
    ∃ (a' C : ℕ) (P : Polynomial ℤ), a' ≤ a ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < Q) ∧
      (∀ n : ℕ, (n : k) ≠ 0 → (Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1} ∧
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1} ≤ C * n ^ (Module.finrank ℤ X + 2 * a')) ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} ∧
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X) ∧
      ∀ y : 𝟙_ (Over (Sp k)) ⟶ N, polyPt (End.of E) P y ≫ E = polyPt (End.of E) P y ^ Q := by
  have : IsCommMonObj N := hN.1
  obtain ⟨hi_hom, hq_hom, hq_flat, hq_surj, hq_aff, hq_pb, _⟩ := id hq
  have := hi_hom
  have := hq_hom
  have := hq_flat
  have := hq_surj
  have := hq_aff
  have : IsMonHom ((𝟙 N) ^ Q) := isMonHom_id_pow N Q
  have hRhom : IsMonHom (E * ((𝟙 N) ^ Q)⁻¹) := isMonHom_mul_degeneration _ _
  have hiq : i ≫ q = 1 := hq_pb.w
  have hiR : i ≫ (E * ((𝟙 N) ^ Q)⁻¹) = toUnit _ ≫ η[N] := by
    rw [(comp_mul_inv_pow_eq_one_iff E Q i).2 hi]
    rfl
  obtain ⟨ψ, hψ, hqψ⟩ := GlobalTheory.FlatQuotient.exists_desc q i (E * ((𝟙 N) ^ Q)⁻¹) hq_pb hiR
  have := hψ
  have hiEq : i ≫ (E ≫ q) = toUnit _ ≫ η[B] := by
    rw [← Category.assoc, hi, MonObj.pow_comp, hiq, one_pow]
    rfl
  obtain ⟨EB, _, hqEB⟩ := GlobalTheory.FlatQuotient.exists_desc q i (E ≫ q) hq_pb hiEq
  have hepi : Epi q := GlobalTheory.FlatQuotient.epi_of_flat_surjective q
  have hψE : EB ≫ ψ = ψ ≫ E := by
    apply hepi.left_cancellation
    rw [← Category.assoc, hqEB, Category.assoc, hqψ, inv_mul_mul_mul_eq_mul, ← Category.assoc, hqψ]
  obtain ⟨B', _, ν, π, hB', hν, hνci, hπν, hstab, hdim⟩ :=
    GlobalTheory.AbelianImage.exists_image k N hN B hB ψ hψ
  have := hν
  have := hνci
  obtain ⟨F', hF', hF'ν⟩ := hstab E inferInstance (fun x => ⟨x ≫ EB, by
    simp only [Category.assoc, hψE]⟩)
  have := hF'
  obtain ⟨a', ha'le, ha'⟩ := hdim a ha
  have hL' : AmpleCub B' (L.pull ν.left) :=
    (GlobalTheory.SS.AmpSub.ampleCub_pull_and_pullPow (Sp k) N L hL).1 B' ν hν hνci
  have hpp : PullPow F'.left (L.pull ν.left) Q :=
    pullPow_pull ν.left (by rw [← Over.comp_left, hF'ν, Over.comp_left]) hE
  obtain ⟨P, _, hProots, hPkill⟩ := GlobalTheory.T.exists_poly_normSq_roots' k B' hB' (L.pull ν.left) hL' (End.of F') Q hF' hpp
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.card_torsion_pullbackPowerLocus_le k N hN X B i q hq hB L hL E Q hQ inferInstance hE hi
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.card_torsion_abelianVariety_le_const_mul_pow k B' hB' (L.pull ν.left) hL' a' ha'
  have hmono : Mono ν := by
    have : Mono ν.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  have : IsMonHom π := by
    have : IsMonHom (π ≫ ν) := by rw [hπν]; infer_instance
    exact GlobalTheory.AbelianImage.isMonHom_of_comp_mono π ν
  have : IsCommMonObj B' := GlobalTheory.AbelianImage.isCommMonObj_of_mono ν
  have hker : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ q ≫ π = 1 → x ≫ E = x ^ Q := by
    intro x hx
    rw [← comp_mul_inv_pow_eq_one_iff, ← hqψ, ← hπν, ← Category.assoc q, ← Category.assoc, hx, MonObj.one_comp]
  refine ⟨a', C2 * (C3 + 1), P, ha'le, fun β hβ => norm_lt_of_normSq hQ (hProots β hβ), ?_, ?_⟩
  · intro n hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [h, Nat.cast_zero]) hn
      · exact h
    obtain ⟨hfin2, hcard2⟩ := hC2 n hn1
    obtain ⟨hfin3, hcard3⟩ := hC3 n hn
    letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ N) := Hom.commGroup
    letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ B') := Hom.commGroup
    let f : (𝟙_ (Over (Sp k)) ⟶ N) →* (𝟙_ (Over (Sp k)) ⟶ B') :=
      { toFun := fun x => x ≫ q ≫ π
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp x y _ }
    let emb : {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} →
        {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} := fun x => ⟨x.1, hker x.1 x.2.1, x.2.2⟩
    have hemb : Function.Injective emb := by
      intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    have : Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} := Finite.of_injective emb hemb
    obtain ⟨hfin, hcard⟩ := card_torsion_le_mul f n
    have hk := Nat.card_le_card_of_injective emb hemb
    refine ⟨⟨hfin, ?_⟩, hfin2, ?_⟩
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1}
          ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} *
              Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ B' // y ^ n = 1} := hcard
        _ ≤ (C2 * n ^ Module.finrank ℤ X) * (C3 * n ^ (2 * a')) := Nat.mul_le_mul (hk.trans hcard2) hcard3
        _ ≤ C2 * (C3 + 1) * n ^ (Module.finrank ℤ X + 2 * a') := by
          rw [pow_add]
          have : C3 ≤ C3 + 1 := Nat.le_succ C3
          calc C2 * n ^ Module.finrank ℤ X * (C3 * n ^ (2 * a'))
              = C2 * C3 * (n ^ Module.finrank ℤ X * n ^ (2 * a')) := by ring
            _ ≤ C2 * (C3 + 1) * (n ^ Module.finrank ℤ X * n ^ (2 * a')) := by gcongr
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1}
          ≤ C2 * n ^ Module.finrank ℤ X := hcard2
        _ ≤ C2 * (C3 + 1) * n ^ Module.finrank ℤ X := by
          gcongr
          exact Nat.le_mul_of_pos_right C2 (Nat.succ_pos C3)
  · intro y
    rw [← comp_mul_inv_pow_eq_one_iff, polyPt_comp (E * ((𝟙 N) ^ Q)⁻¹) (End.of E) (End.of E) (inv_mul_mul_mul_eq_mul E Q) P y, ← hqψ, ← hπν,
      show y ≫ q ≫ π ≫ ν = ((y ≫ q) ≫ π) ≫ ν by simp only [Category.assoc],
      ← polyPt_comp ν (End.of F') (End.of E) hF'ν P, hPkill, MonObj.one_comp]

private theorem isClosedImmersion_of_isPullback_unit {k : Type} [Field k] {T N B : Over (Sp k)} [GrpObj B] [IsSeparated B.hom]
    (i : T ⟶ N) (q : N ⟶ B) (h : IsPullback i (toUnit T) q η[B]) : IsClosedImmersion i.left := by
  have hη : IsClosedImmersion (η[B]).left := by
    have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
      rw [Over.w]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp k)))
    exact IsClosedImmersion.of_comp _ B.hom
  have h' : IsPullback i.left (toUnit T).left q.left (η[B]).left := h.map (Over.forget (Sp k))
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h'.flip hη

private theorem eq_of_comp_mono_eq {k : Type} [Field k] {N G : Over (Sp k)} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [Mono ν]
    {x y : 𝟙_ (Over (Sp k)) ⟶ N} (h : x ≫ ν = y ≫ ν) : x = y := by
  exact (cancel_mono ν).1 h

end GlobalTheory.SS.FrobTorsion


open GlobalTheory.SS.FrobTorsion in
theorem GlobalTheory.SS.frobenius_on_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [CharP k p], l.Prime → l ≠ p → ∀ (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : End G) (q : ℕ), 2 ≤ q → FrobG G F q → ∃ (t a m C : ℕ) (P : Polynomial ℤ) (W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)), 1 ≤ m ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < (q : ℝ) ^ m) ∧ (∀ x ∈ W, x ≫ (F ^ m).asHom = x ^ (q ^ m)) ∧ (∀ n, Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) n, x ^ l ^ n = 1 → polyPt (F ^ m) P x ∈ W) ∧ (g ≤ t + a → Nonempty (TorusExtension G)) := by
  intro k _ _ p l _ _ hl hlp G _ hG g hg L hL F q hq hF
  have : IsCommMonObj G := hG.1
  letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  obtain ⟨N, _, ν, hN, hν, hνci, hdiv, hlift, hFlift, hdimN⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  have := hν
  have := hνci
  have : IsCommMonObj N := hN.1
  letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ N) := Hom.commGroup
  obtain ⟨F', hF', hF'ν⟩ := hFlift F.asHom hF.1
  have := hF'
  have hνmono : Mono ν := by
    have : Mono ν.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  let F'e : End N := End.of F'
  obtain ⟨g', hg', hgiso⟩ := hdimN g hg
  obtain ⟨X, _, _, _, B, _, i, qB, hqB, hB, hdimB⟩ := GlobalTheory.T.exists_torus_abelian_quotient_p_divisible_smooth_group k p N hN hdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'
  have hFN : FrobG N F'e q :=
    (GlobalTheory.SS.frobG_pow_and_closed_subgroup k G hG F q hF).2 N ν F'e hν hνci hF' hF'ν
  obtain ⟨hi_hom, hq_hom, hq_flat, hq_surj, hq_aff, hq_pb, _⟩ := id hqB
  have := hi_hom
  have := hq_hom
  have : IsProper B.hom := hB.proper
  have htriv : i ≫ F' ≫ qB = toUnit _ ≫ η[B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_field k X B (i ≫ F' ≫ qB) inferInstance
  let F'' : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X :=
    hq_pb.lift (i ≫ F') (toUnit _) (by rw [Category.assoc, htriv])
  have hF''i : F'' ≫ i = i ≫ F' := hq_pb.lift_fst _ _ _
  have : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  have hi_mono : Mono i := hq_pb.mono_fst_of_mono
  have : IsMonHom (F'' ≫ i) := by rw [hF''i]; infer_instance
  have hF''hom : IsMonHom F'' := GlobalTheory.AbelianImage.isMonHom_of_comp_mono F'' i
  have : IsClosedImmersion i.left := isClosedImmersion_of_isPullback_unit i qB hq_pb
  let F''e : End (splitTorus (Sp k) X) := End.of F''
  have hFT : FrobG (splitTorus (Sp k) X) F''e q :=
    (GlobalTheory.SS.frobG_pow_and_closed_subgroup k N hN F'e q hFN).2 _ i F''e hi_hom inferInstance hF''hom hF''i
  obtain ⟨m1, hm1, hpow1⟩ := GlobalTheory.SS.frobG_splitTorus_pow k X F''e q hFT
  have hLN : AmpleCub N (L.pull ν.left) :=
    (GlobalTheory.SS.AmpSub.ampleCub_pull_and_pullPow (Sp k) G L hL).1 N ν hν hνci
  obtain ⟨m2, hm2, hpow2⟩ := GlobalTheory.SS.FrobLB.frob_pullPow k N hN F'e q hFN (L.pull ν.left) hLN.1
  have hM : 1 ≤ m1 * m2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hEhom : IsMonHom (F'e ^ (m1 * m2)).asHom := GlobalTheory.SS.FrobSub.isMonHom_pow N F'e hF' (m1 * m2)
  have hQ : 2 ≤ q ^ (m1 * m2) := le_trans hq (Nat.le_self_pow (by omega) q)
  have hE : PullPow (F'e ^ (m1 * m2)).asHom.left (L.pull ν.left) ((q ^ (m1 * m2) : ℕ) : ℤ) := by
    have h := hpow2 m1
    rw [show m2 * m1 = m1 * m2 from Nat.mul_comm _ _] at h
    rw [Nat.cast_pow]
    exact h
  have hiE : i ≫ (F'e ^ (m1 * m2)).asHom = i ^ (q ^ (m1 * m2)) := by
    rw [← GlobalTheory.SS.FrobSub.pow_comm_hom i F'e F''e hF''i (m1 * m2), hpow1 m2, MonObj.pow_comp, Category.id_comp]
  obtain ⟨a', C, P, ha'le, hroots, hbounds, hfix⟩ :=
    core k N hN X B i qB hqB hB (L.pull ν.left) hLN (F'e ^ (m1 * m2)).asHom (q ^ (m1 * m2)) hQ hE hiE a ha
  have hcomm : (F'e ^ (m1 * m2)).asHom ≫ ν = ν ≫ (F ^ (m1 * m2)).asHom :=
    GlobalTheory.SS.FrobSub.pow_comm_hom ν F F'e hF'ν (m1 * m2)
  have hFM : IsMonHom (F ^ (m1 * m2)).asHom := GlobalTheory.SS.FrobSub.isMonHom_pow G F hF.1 (m1 * m2)
  let W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | x ≫ (F ^ (m1 * m2)).asHom = x ^ (q ^ (m1 * m2))}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [MonObj.mul_comp, hx, hy, mul_pow]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [MonObj.one_comp, one_pow]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [GrpObj.inv_comp, hx, inv_pow] }
  have hlk : ∀ n : ℕ, ((l ^ n : ℕ) : k) ≠ 0 := by
    intro n h
    rw [Nat.cast_pow] at h
    have h1 : ((l : ℕ) : k) = 0 := pow_eq_zero_iff'.mp h |>.1
    rw [CharP.cast_eq_zero_iff k p] at h1
    exact hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hl).mp h1).symm
  have hcop : ∀ n : ℕ, (l ^ n).Coprime p := fun n =>
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl (Fact.out)).2 hlp)
  have hlpos : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n hl.ne_zero
  have hlift' : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ G) (n : ℕ), x ^ l ^ n = 1 →
      ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ l ^ n = 1 := by
    intro x n hx
    obtain ⟨y, hy⟩ := hlift x (l ^ n) (hcop n) (hlpos n) hx
    refine ⟨y, hy, eq_of_comp_mono_eq ν ?_⟩
    rw [MonObj.pow_comp, hy, hx, MonObj.one_comp]
  refine ⟨Module.finrank ℤ X, a', m1 * m2, C, P, W, hM, ?_, fun x hx => hx, ?_, ?_, ?_⟩
  · intro β hβ
    have := hroots β hβ
    push_cast at this
    exact this
  · intro n
    obtain ⟨⟨hfinN, hcardN⟩, hfinF, hcardF⟩ := hbounds (l ^ n) (hlk n)
    let f1 : {y : 𝟙_ (Over (Sp k)) ⟶ N // y ^ l ^ n = 1} → {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1} :=
      fun y => ⟨y.1 ≫ ν, by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]⟩
    have hf1 : Function.Surjective f1 := by
      intro x
      obtain ⟨y, hy, hyn⟩ := hlift' x.1 n x.2
      exact ⟨⟨y, hyn⟩, Subtype.ext hy⟩
    let f2 : {y : 𝟙_ (Over (Sp k)) ⟶ N // y ≫ (F'e ^ (m1 * m2)).asHom = y ^ (q ^ (m1 * m2)) ∧ y ^ l ^ n = 1} →
        {x : W // x ^ l ^ n = 1} :=
      fun y => ⟨⟨y.1 ≫ ν, by
          show (y.1 ≫ ν) ≫ (F ^ (m1 * m2)).asHom = (y.1 ≫ ν) ^ (q ^ (m1 * m2))
          rw [Category.assoc, ← hcomm, ← Category.assoc, y.2.1, MonObj.pow_comp]⟩, by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow]
        show (y.1 ≫ ν) ^ l ^ n = 1
        rw [← MonObj.pow_comp, y.2.2, MonObj.one_comp]⟩
    have hf2 : Function.Surjective f2 := by
      intro x
      have hxn : (x.1 : 𝟙_ (Over (Sp k)) ⟶ G) ^ l ^ n = 1 := by
        rw [← SubgroupClass.coe_pow, x.2]
        rfl
      obtain ⟨y, hy, hyn⟩ := hlift' x.1.1 n hxn
      have hyE : y ≫ (F'e ^ (m1 * m2)).asHom = y ^ (q ^ (m1 * m2)) := by
        apply eq_of_comp_mono_eq ν
        rw [Category.assoc, hcomm, ← Category.assoc, hy, MonObj.pow_comp, hy]
        exact x.1.2
      exact ⟨⟨y, hyE, hyn⟩, Subtype.ext (Subtype.ext hy)⟩
    have : Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1} := Finite.of_surjective f1 hf1
    refine ⟨inferInstance, ?_, ?_⟩
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1}
          ≤ Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ N // y ^ l ^ n = 1} := Nat.card_le_card_of_surjective f1 hf1
        _ ≤ C * (l ^ n) ^ (Module.finrank ℤ X + 2 * a') := hcardN
        _ = C * l ^ (n * (Module.finrank ℤ X + 2 * a')) := by rw [← pow_mul]
    · calc Nat.card {x : W // x ^ l ^ n = 1}
          ≤ Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ N //
              y ≫ (F'e ^ (m1 * m2)).asHom = y ^ (q ^ (m1 * m2)) ∧ y ^ l ^ n = 1} :=
            Nat.card_le_card_of_surjective f2 hf2
        _ ≤ C * (l ^ n) ^ Module.finrank ℤ X := hcardF
        _ = C * l ^ (n * Module.finrank ℤ X) := by rw [← pow_mul]
  · intro x n hx
    obtain ⟨y, hy, _⟩ := hlift' x n hx
    show polyPt (F ^ (m1 * m2)) P x ≫ (F ^ (m1 * m2)).asHom = (polyPt (F ^ (m1 * m2)) P x) ^ (q ^ (m1 * m2))
    rw [← hy, ← polyPt_comp ν (F'e ^ (m1 * m2)) (F ^ (m1 * m2)) hcomm P y, Category.assoc, ← hcomm,
      ← Category.assoc, hfix y, MonObj.pow_comp]
  · intro hle
    have hgg : g ≤ g' := by omega
    have := hgiso hgg
    have : QuasiCompact qB.left := inferInstance
    let T : TorusExtension N :=
      { X := X, B := B, isAbelian := hB, q := qB, q_hom := hq_hom, q_flat := hq_flat,
        q_surjective := hq_surj, q_quasiCompact := inferInstance, i := i, i_hom := hi_hom, isKernel := hq_pb }
    exact ⟨torusExtOfIso (asIso ν) T⟩

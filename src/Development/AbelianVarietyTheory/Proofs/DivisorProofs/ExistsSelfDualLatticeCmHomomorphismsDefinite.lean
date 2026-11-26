module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImages

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLinearHomSpanGramForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLinearHomSpanGramForm
set_option autoImplicit false

noncomputable section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

section Calc

variable {S : Scheme.{0}} {X Y A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] {L : LB A.left} {M : LB B.left} {N : LB C.left}

theorem lamEq_symm' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq M g₁ g₂ L f₁ f₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).1

theorem lamEq_swap' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq L f₂ f₁ M g₂ g₁ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.1

theorem lamEq_trans' (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B}
    {g₂ : Y ⟶ B} {k₁ : X ⟶ C} {k₂ : Y ⟶ C} (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq M g₁ g₂ N k₁ k₂) :
    LamEq L f₁ f₂ N k₁ k₂ :=
  ((LamCalc.lamEq_calculus S X Y A B C L M N hL hM hN f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ k₁ k₂).2.1 h).2.2.1 h'

theorem lamEq_pre (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) {X' Y' : Over S} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂) :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.2.2.1 X' Y' a b

variable (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen)
include hL hM hT hT'

theorem lamEq_mul_left' {f₁ f₁' : X ⟶ A} {f₂ : Y ⟶ A} {g₁ g₁' : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq L f₁' f₂ M g₁' g₂) : LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁' f₂ f₂ g₁ g₁' g₂ g₂ g₁ g₂).2.2.1 hT hT' h).1 h'

theorem lamEq_prod_left {J : Type} (s : Finset J) (f : J → (X ⟶ A)) (g : J → (X ⟶ B)) (f₂ : Y ⟶ A) (g₂ : Y ⟶ B)
    (h0 : LamEq L (1 : X ⟶ A) f₂ M (1 : X ⟶ B) g₂) (h : ∀ i ∈ s, LamEq L (f i) f₂ M (g i) g₂) :
    LamEq L (s.prod f) f₂ M (s.prod g) g₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM (f i) (s.prod f) f₂ f₂ (g i) (s.prod g) g₂ g₂
      (g i) g₂).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).1
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lamEq_prod_right {J : Type} (s : Finset J) (f₁ : X ⟶ A) (g₁ : X ⟶ B) (f : J → (Y ⟶ A)) (g : J → (Y ⟶ B))
    (h0 : LamEq L f₁ (1 : Y ⟶ A) M g₁ (1 : Y ⟶ B)) (h : ∀ i ∈ s, LamEq L f₁ (f i) M g₁ (g i)) :
    LamEq L f₁ (s.prod f) M g₁ (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ (f i) (s.prod f) g₁ g₁ (g i) (s.prod g)
      g₁ (g i)).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).2
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Calc

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G)

theorem act_zero' : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have := congrArg (fun u => (act.act 0)⁻¹ * u) h
  simpa using this.symm

theorem act_sum' {J : Type} (s : Finset J) (c : J → O) : act.act (s.sum c) = s.prod fun i : J => act.act (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using act_zero' act
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, act.add, ih]

end Act

theorem exists_thetaGen' (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  exact ⟨c.t, c.isGen⟩

theorem weilEq_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG m hm z f hf hfm x r hr
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have hβ : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have lA : (X.A true).t.PP.L.IsLB := (X.A true).t.PP.isLB
  have lB : X.B.t.PP.L.IsLB := X.B.t.PP.isLB
  have tA := exists_thetaGen' hL (X.A true).pol
  have tB := exists_thetaGen' hL X.B.pol
  haveI : IsMonHom f := hf.1
  haveI hφ : ∀ a, IsMonHom (phiP X a) := fun a => (X.lin (Sum.inl a)).1
  haveI hact : ∀ s, IsMonHom ((X.A true).t.act.act s) := (X.A true).t.act.hom
  have toLam : ∀ (f₁ f₂ : (X.A true).t.G ⟶ X.B.t.G) (g₁ g₂ : (X.A true).t.G ⟶ (X.A true).t.G), IsMonHom f₁ →
      IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
      WeilEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
      LamEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ := fun f₁ f₂ g₁ g₂ h₁ h₂ h₃ h₄ h =>
    (PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol (X.A true).pol f₁ f₂ g₁ g₂
      h₁ h₂ h₃ h₄ ℂ _).2 inferInstance hβ h

  have E1 : ∀ a b, LamEq X.B.t.PP.L ((X.A true).t.act.act (z a) ≫ phiP X a) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro a b
    have := lamEq_pre lB lA (toLam _ _ _ _ (hφ a) (hφ b) (hact _) inferInstance (hG.1 a b))
      ((X.A true).t.act.act (z a)) ((X.A true).t.act.act (x b))
    rwa [← (X.A true).t.act.mul, Category.comp_id] at this

  have S1 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro b
    have h0 : LamEq X.B.t.PP.L (1 : (X.A true).t.G ⟶ X.B.t.G) ((X.A true).t.act.act (x b) ≫ phiP X b)
        (X.A true).t.PP.L (1 : (X.A true).t.G ⟶ (X.A true).t.G) ((X.A true).t.act.act (x b)) := by
      have := lamEq_pre lB lA (E1 b b) (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
    have := lamEq_prod_left lB lA tB tA Finset.univ (fun a => (X.A true).t.act.act (z a) ≫ phiP X a)
      (fun a => (X.A true).t.act.act (z a * gP a b)) _ _ h0 (fun a _ => E1 a b)
    rwa [← hfm, ← act_sum'] at this

  have M1 : ∀ t y : 𝓞 E, LamEq (X.A true).t.PP.L ((X.A true).t.act.act t) ((X.A true).t.act.act y)
      (X.A true).t.PP.L ((X.A true).t.act.act (t * H.bar y)) (𝟙 _) := by
    intro t y
    have h2 := lamEq_pre lA lA (lamEq_swap' lA lA (LamF.lamEq_adj (X.A true).t y)) ((X.A true).t.act.act t) (𝟙 _)
    rwa [Category.comp_id, Category.id_comp, Category.id_comp, ← (X.A true).t.act.mul] at h2
  have F2 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b) (X.A true).t.PP.L (𝟙 _)
      ((X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) := fun b =>
    lamEq_trans' lB lA lA (lamEq_trans' lB lA lA (S1 b) (M1 _ _)) (LamF.lamEq_adj (X.A true).t _)

  obtain ⟨r', hr'⟩ := GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f
    (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) hf (isLinearHom_prod X x)
  haveI hψ : IsMonHom (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) := (isLinearHom_prod X x).1
  have R := toLam _ _ _ _ inferInstance hψ (hact r') inferInstance hr'
  have Rm : ∀ n : ℕ, LamEq X.B.t.PP.L (f ^ n) (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act ((n : 𝓞 E) * r')) (𝟙 _) := by
    intro n
    induction n with
    | zero =>
      have := lamEq_pre lB lA R (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rw [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
      rwa [pow_zero, Nat.cast_zero, zero_mul, act_zero']
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, _root_.one_mul, (X.A true).t.act.add]
      exact lamEq_mul_left' lB lA tB tA ih R
  have RmA := lamEq_trans' lB lA lA (Rm m) (LamF.lamEq_adj (X.A true).t ((m : 𝓞 E) * r'))
  have base2 : LamEq X.B.t.PP.L (f ^ m) (1 : (X.A true).t.G ⟶ X.B.t.G) (X.A true).t.PP.L (𝟙 _)
      (1 : (X.A true).t.G ⟶ (X.A true).t.G) := by
    have := lamEq_pre lB lA RmA (𝟙 _) (1 : (X.A true).t.G ⟶ (X.A true).t.G)
    rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
  have S2 := lamEq_prod_right lB lA tB tA Finset.univ (f ^ m) (𝟙 _)
    (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) base2 (fun b _ => F2 b)
  have hsum : (∑ b, H.bar ((∑ a, z a * gP a b) * H.bar (x b))) = H.bar ((m : 𝓞 E) * r) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [← act_sum', hsum] at S2

  have U := lamEq_swap' lA lA (lamEq_trans' lA lB lA (lamEq_symm' lB lA S2) RmA)
  have e₁ := PairingInj.eq_of_lamEq hL _ (X.A true).pol _ _ _ U
  have hg : 1 ≤ (X.A true).pol.g := NumInh.dim_pos_of_hasType X.split X.ρ_sq (X.A true) X.typeP
  have e₂ := H.bar.injective (LamF.Faithful.act_injective hL E K (X.A true).pol (X.A true).t.act hg e₁)
  have e₃ : r = r' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne' : (m : 𝓞 E) ≠ 0) e₂
  rw [e₃]
  exact hr'

end GlobalTheory.FlatCM.HomLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLinearHomSpanGramFormStatement
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_linearHom_span_gramForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.FlatCM.HomLat.weilEq_gram | exact GlobalTheory.FlatCM.HomLat.weilEq_gram | (intros; apply GlobalTheory.FlatCM.HomLat.weilEq_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearHomPowEqOfKillsComplexTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearHomPowEqOfKillsComplexTorsion
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DivisibleLinear

variable {S S' : Scheme.{0}}

theorem eq_one_iff {G T : Over S} [GrpObj G] (z : T ⟶ G) : z = 1 ↔ z.left = T.hom ≫ η[G].left := by
  have hu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  constructor
  · rintro rfl
    rw [Hom.one_def, Over.comp_left, hu]
  · intro h
    apply Over.OverMorphism.ext
    rw [h, Hom.one_def, Over.comp_left, hu]

section BaseChange

variable {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'}
    (h : Out.toBase hg.w x = Out.toBase hg.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.hom_ext
  · simpa [Out.toBase] using congrArg (·.left) h
  · rw [Over.w x, Over.w y]

variable (hg : IsPullback g G'.hom G.hom f)
  (hm : ∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hg.w (x * y) = Out.toBase hg.w x * Out.toBase hg.w y)
include hm

theorem toBase_one (T : Over S') : Out.toBase hg.w (1 : T ⟶ G') = 1 := by
  have h := hm T 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.mp h.symm

theorem toBase_pow {T : Over S'} (x : T ⟶ G') (n : ℕ) : Out.toBase hg.w (x ^ n) = Out.toBase hg.w x ^ n := by
  induction n with
  | zero => simpa using toBase_one hg hm T
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

end BaseChange

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem torsion_comp_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (P Q : Out.PolAV (Sp (𝓞 K))) (ψ : P.A ⟶ Q.A) [IsMonHom ψ] (n : ℕ) (hn : 0 < n)
    (h : ∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, u ^ n = 1 → u ≫ ψ = 1)
    (T : Over (Sp (𝓞 K))) (x : T ⟶ P.A) (hx : x ^ n = 1) : x ≫ ψ = 1 := by
  set gc : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K) with hgc
  set t : Sp ℂ ⟶ Sp (𝓞 K) := spMap gc with ht
  have hgci : Function.Injective gc :=
    σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨P', gA, hgA, -, hmA, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t P
  obtain ⟨Q', gB, hgB, -, hmB, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t Q
  have := Q.isAb.proper
  have := Q'.isAb.proper

  let ψ' : P'.A ⟶ Q'.A := Over.homMk (hgB.lift (gA ≫ ψ.left) P'.A.hom
    (by rw [Category.assoc, Over.w ψ, hgA.w])) (hgB.lift_snd _ _ _)
  have tb : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A),
      Out.toBase hgB.w (y ≫ ψ') = Out.toBase hgA.w y ≫ ψ := by
    intro T' y
    apply Over.OverMorphism.ext
    simp [Out.toBase, ψ']
  have : IsMonHom ψ' := GlobalTheory.DivisibleHom.isMonHom_of_mul_points ψ' fun T' y₁ y₂ =>
    toBase_injective hgB (by rw [tb, hmA, MonObj.mul_comp, hmB, tb, tb])

  have hC : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, y ^ n = 1 → y ≫ ψ' = 1 := by
    intro y hy
    let e : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ t) := Over.homMk (𝟙 _) (by simp)
    have h1 : (e ≫ Out.toBase hgA.w y) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← toBase_pow hgA hmA, hy, toBase_one hgA hmA, MonObj.comp_one]
    have h2 := h _ h1
    apply toBase_injective hgB
    rw [tb, toBase_one hgB hmB, eq_one_iff]
    have h3 := (eq_one_iff _).1 h2
    simpa [e] using h3
  obtain ⟨α, hα, hfac⟩ := GlobalTheory.HolUnifEnd.exists_factor_pow P'.A Q'.A P'.isAb n hn ψ' hC
  have kill' : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A), y ^ n = 1 → y ≫ ψ' = 1 := by
    intro T' y hy
    rw [← hfac, ← Category.assoc, MonObj.comp_pow, Category.comp_id, hy, MonObj.one_comp]

  obtain ⟨_, hfl, _, _, -⟩ := hL.mulN (Sp (𝓞 K)) P n hn
  let Z := pullback (Out.mulA P.A n) η[P.A]
  let inc : Z ⟶ P.A := pullback.fst (Out.mulA P.A n) η[P.A]
  have hinc : inc ^ n = 1 := by
    rw [← GlobalTheory.DivisibleHom.comp_mulA, pullback.condition, Hom.one_def,
      toUnit_unique (pullback.snd (Out.mulA P.A n) η[P.A]) (toUnit Z)]
  have hp := (IsPullback.of_hasPullback (Out.mulA P.A n) η[P.A]).map (Over.forget (Sp (𝓞 K)))
  have hf : Flat (pullback.snd (Out.mulA P.A n) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hfl
  have hw : (pullback.snd (Out.mulA P.A n) η[P.A]).left = Z.hom := by
    simpa using Over.w (pullback.snd (Out.mulA P.A n) η[P.A])
  rw [hw] at hf
  have hx' : x ≫ Out.mulA P.A n = toUnit T ≫ η[P.A] := by
    rw [GlobalTheory.DivisibleHom.comp_mulA, hx, Hom.one_def]
  suffices hZ : inc ≫ ψ = 1 by
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ ψ = 1
    rw [hZ, MonObj.comp_one]
  rw [eq_one_iff]
  refine GlobalTheory.ArcDataDescent.ext_of_injective hgci (IsPullback.of_hasPullback Z.hom t) Q.A.hom ?_ ?_
  · simp
  · let π := pullback.fst Z.hom t
    let p' := pullback.snd Z.hom t
    let w := hgA.lift (π ≫ inc.left) p' (by rw [Category.assoc, Over.w inc, pullback.condition])
    let x' : Over.mk p' ⟶ P'.A := Over.homMk w (hgA.lift_snd _ _ _)
    let πZ : Over.mk (p' ≫ t) ⟶ Z := Over.homMk π pullback.condition
    have hb : Out.toBase hgA.w x' = πZ ≫ inc := by
      apply Over.OverMorphism.ext
      simp [Out.toBase, x', w, πZ]
    have hx'n : x' ^ n = 1 := by
      apply toBase_injective hgA
      rw [toBase_pow hgA hmA, hb, ← MonObj.comp_pow, hinc, MonObj.comp_one, toBase_one hgA hmA]
    have k2 := congrArg (Out.toBase hgB.w) (kill' _ x' hx'n)
    rw [tb, toBase_one hgB hmB, hb, eq_one_iff] at k2
    simp only [Over.comp_left] at k2 ⊢
    rw [pullback.condition_assoc]
    simpa [πZ] using k2

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  intro E _ _ _ H K _ _ σ A B ψ hψ n hn hk
  have := hψ.isMonHom
  have hker := torsion_comp_eq_one σ A.pol B.pol ψ n hn hk
  obtain ⟨⟨χ, hχ, hχψ⟩, -⟩ := GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
    (fun S _ P m hm => by
      obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN S P m hm
      exact ⟨h1, h2, h3, h4⟩)
    (Sp (𝓞 K)) A.pol B.t.G n hn ψ hψ.isMonHom hker
  refine ⟨χ, ⟨hχ, fun c => ?_⟩, hχψ.symm⟩
  have := B.t.act.hom c
  have := A.t.act.hom c
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol n hn
  have : Flat (Out.mulA A.t.G n).left := hfl
  have : Surjective (Out.mulA A.t.G n).left := hsu
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (Out.mulA A.t.G n)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, ← MonObj.comp_pow, ← hχψ, hψ.comm c, hχψ,
    MonObj.pow_comp]

end GlobalTheory.DivisibleLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearHomPowEqOfKillsComplexTorsionStatement
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  first | exact @GlobalTheory.DivisibleLinear.exists_linear_pow_eq | exact GlobalTheory.DivisibleLinear.exists_linear_pow_eq | (intros; apply GlobalTheory.DivisibleLinear.exists_linear_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, GlobalTheory.T.weilPairing_linearHom_span_gramForm E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairingStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  first | exact @GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | exact GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | (intros; apply GlobalTheory.FlatCM.HomLat.mem_lat_of_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHomGramFormIntegralCoordinateLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddFirstSlotComplexStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddLeftComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.WeilAddLeft

theorem pow_comp_hom {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul (Units.map _) u v

theorem weilEq_mul_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm
  haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm
  have tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1) := fun f hf => by
    rw [← pow_comp_hom, hx, one_comp]
  have tory : (y ≫ g) ^ n = 1 := by rw [← pow_comp_hom, hy, one_comp]
  obtain ⟨c₁, hc₁⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory
  obtain ⟨c₂, hc₂⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory
  have a₁ := (h₁ n x y c₁ hn hx hy).1 hc₁
  have a₂ := (h₂ n x y c₂ hn hx hy).1 hc₂
  have hB := weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂
  have hA := weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂
  rw [← MonObj.comp_mul] at hB hA
  rw [← A.t.act.add] at hA
  rw [← unitOn_mul] at hB hA
  constructor
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory.CM.WeilAddLeft
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_add_first_position_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.CM.WeilAddLeft.weilEq_mul_left | exact GlobalTheory.CM.WeilAddLeft.weilEq_mul_left | (intros; apply GlobalTheory.CM.WeilAddLeft.weilEq_mul_left <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHomGramFormIntegralCoordinateLattice
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.GramInt

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

theorem weilEq_act_left {A B : PAT H (Sp (𝓞 K))} {f g : A.t.G ⟶ B.t.G} {r : 𝓞 E} {k : Type} [Field k]
    {t : Sp k ⟶ Sp (𝓞 K)} (s : 𝓞 E) (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) t) :
    WeilEq B.t.PP.L (A.t.act.act s ≫ f) g A.t.PP.L (A.t.act.act (s * r)) (𝟙 _) t := by
  intro n x y c hn hx hy
  haveI := A.t.act.hom s
  have hx' : (x ≫ A.t.act.act s) ^ n = 1 := by rw [← pow_comp, hx]; simp
  have := h n (x ≫ A.t.act.act s) y c hn hx' hy
  simpa only [Category.assoc, A.t.act.mul] using this
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem isLinearHom_finprod {I₀ : Type} (S : Finset I₀) (F : I₀ → (A.t.G ⟶ B.t.G))
    (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i)) :
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ S, F i) :=
  Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
    (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hF i

theorem weilEq_prod_right {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf.isMonHom (hG a).isMonHom
      (isLinearHom_finprod s G hG).isMonHom _ _ (h a) ih

theorem weilEq_prod_prod {I₀ J₀ : Type} (F : I₀ → (A.t.G ⟶ B.t.G)) (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i))
    (G : J₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ j, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G j)) (r : I₀ → J₀ → 𝓞 E)
    (h : ∀ i j, WeilEq B.t.PP.L (F i) (G j) A.t.PP.L (A.t.act.act (r i j)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {S : Finset I₀} (hS : S.Nonempty) {T : Finset J₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L (∏ i ∈ S, F i) (∏ j ∈ T, G j) A.t.PP.L (A.t.act.act (∑ i ∈ S, ∑ j ∈ T, r i j)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simpa using weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_first_position_complex E H K σ₁ A B (F a) _ _ (hF a).isMonHom (isLinearHom_finprod s F hF).isMonHom
      (isLinearHom_finprod T G hG).isMonHom _ _ (weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT) ih

theorem weilEq_pow_pow (f g : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (hg : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act g) (r : 𝓞 E)
    (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    WeilEq B.t.PP.L (f ^ n) (g ^ m) A.t.PP.L (A.t.act.act ((n * m : ℕ) * r)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have e1 : f ^ n = ∏ _i ∈ Finset.range n, f := by simp
  have e2 : g ^ m = ∏ _j ∈ Finset.range m, g := by simp
  have e3 : ((n * m : ℕ) : 𝓞 E) * r = ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range m, r := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [e1, e2, e3]
  exact weilEq_prod_prod (fun _ => f) (fun _ => hf) (fun _ => g) (fun _ => hg) (fun _ _ => r) (fun _ _ => h)
    (Finset.nonempty_range_iff.2 hn.ne') (Finset.nonempty_range_iff.2 hm.ne')
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p : ℕ}

theorem weilEq_combo (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (hp : 0 < p) (x y : Fin p → 𝓞 E) :
    WeilEq X.B.t.PP.L (∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a))
      (∏ b, ((X.A true).t.act.act (y b) ≫ GlobalTheory.FlatCM.phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hp⟩⟩
  have hlin : ∀ (z : Fin p → 𝓞 E) a, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act
      ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) := fun z a =>
    (GlobalTheory.Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))
  refine weilEq_prod_prod _ (hlin x) _ (hlin y) _ (fun a b => ?_) hne hne
  have h1 := weilEq_act_left (x a) (hG.1 a b)
  exact GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hlin x a).isMonHom (X.lin (Sum.inl b)).isMonHom _ (y b) h1

theorem integral_of_coords (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (barE : E →+* E)
    (hbar : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) {c d : Fin p → E}
    (hc : c ∈ GlobalTheory.FlatCM.HomLat.coords X) (hd : d ∈ GlobalTheory.FlatCM.HomLat.coords X) :
    ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn, x, hx, f, hf, hfx⟩ := hc
  obtain ⟨m, hm, y, hy, g, hg, hgy⟩ := hd
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    f g hf hg
  have h1 := weilEq_pow_pow f g hf hg r hr hn hm
  rw [hfx, hgy] at h1
  have h2 := weilEq_combo X gP gQ hG hp x y
  have h3 : WeilEq (X.A true).t.PP.L ((X.A true).t.act.act ((n * m : ℕ) * r)) (𝟙 _) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)
  have h4 := GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ h3
  refine ⟨r, ?_⟩
  have h5 := congrArg (fun z : 𝓞 E => (z : E)) h4
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_natCast, map_sum] at h5
  have hnm : ((n * m : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne'
  apply mul_left_cancel₀ hnm
  rw [h5]
  simp only [hx, hy, ← hbar, map_mul, map_natCast, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end

theorem gram_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG barE hbar c hc d hd

  have step : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
      ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
    intro c hc d hd
    induction hd using Submodule.span_induction with
    | mem d hd => exact integral_of_coords X gP gQ hG barE hbar hc hd
    | zero => exact ⟨0, by simp⟩
    | add d d' _ _ h h' =>
      obtain ⟨y, hy⟩ := h
      obtain ⟨y', hy'⟩ := h'
      refine ⟨y + y', ?_⟩
      simp only [map_add (f := _), hy, hy', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul s d _ h =>
      obtain ⟨y, hy⟩ := h
      refine ⟨H.bar s * y, ?_⟩
      simp only [map_mul, ← hbar, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  induction hc using Submodule.span_induction with
  | mem c hc => exact step c hc d hd
  | zero => exact ⟨0, by simp⟩
  | add c c' _ _ h h' =>
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', hy'⟩ := h'
    refine ⟨y + y', ?_⟩
    simp only [map_add (f := _), hy, hy', Pi.add_apply, add_mul, Finset.sum_add_distrib]
  | smul s c _ h =>
    obtain ⟨y, hy⟩ := h
    refine ⟨s * y, ?_⟩
    simp only [map_mul, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.FlatCM.GramInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHomGramFormIntegralCoordinateLatticeStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHomGramForm_integral_coordinateLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  first | exact @GlobalTheory.FlatCM.GramInt.gram_integral | exact GlobalTheory.FlatCM.GramInt.gram_integral | (intros; apply GlobalTheory.FlatCM.GramInt.gram_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSmulDifferentialMemEigenLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSmulDifferentialMemEigenLattice
open NumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM GlobalTheory.CM.IntCoord

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat

theorem sum_smul_diff_mem_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he
  obtain ⟨n, hn, x, hx, f, hf, hfn⟩ := hc
  have hcA := integral_tangent_coordinates K _ FP
  have hcB := integral_tangent_coordinates K _ FB
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have := hf.isMonHom
  have ht : IsTangent (u ≫ f) := by
    have hv := hu.1
    unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨d, hd, -⟩ := hcB.1 _ ht
  have hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FP hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have heq : n • d = ∑ a, MP a (τ (x a) • e) := by
    have h1 := hpow n
    rw [← comp_pow, hfn] at h1
    exact (hcB.1 _ h1.1).unique h1 (hprod Finset.univ)
  have hdval : d = ∑ a, τE (c a) • MP a e := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine smul_right_injective _ hn0 ?_
    show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e
    rw [Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]
    congr 1
    show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)
    rw [← hτE, hx a, map_mul, map_natCast]
  rw [← hdval]
  refine (hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s),
    Category.assoc]

end GlobalTheory.FlatCM.HomLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSmulDifferentialMemEigenLatticeStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_smul_differential_mem_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  first | exact @GlobalTheory.FlatCM.HomLat.sum_smul_diff_mem_eigLat | exact GlobalTheory.FlatCM.HomLat.sum_smul_diff_mem_eigLat | (intros; apply GlobalTheory.FlatCM.HomLat.sum_smul_diff_mem_eigLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefinite
set_option autoImplicit false

open NumberField

namespace GlobalTheory.FlatCM.HomLat

theorem exists_selfDual_lieSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG
  refine ⟨GlobalTheory.FlatCM.HomLat.lat X, GlobalTheory.T.cmLinearHomCoordinateLattice_fg E H hH K ρ σ₁ p X, GlobalTheory.FlatCM.HomLat.intl_mem X,
    fun barE hbar d => ⟨fun hd c hc => GlobalTheory.T.cmHomGramForm_integral_coordinateLattice E H hH K ρ σ₁ p X gP gQ hG barE hbar c hc d hd,
      GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing E H hH K ρ σ₁ p X gP gQ hG barE hbar d⟩, ?_⟩
  intro FP FB MP hMP τ hτ τE hτE
  refine le_antisymm (GlobalTheory.T.lieEigenLattice_le_span_cmHom_images E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE) ?_
  refine Submodule.span_le.2 ?_
  rintro w ⟨c, hc, e, he, rfl⟩
  induction hc using Submodule.span_induction generalizing e with
  | mem c hc => exact GlobalTheory.T.sum_smul_differential_mem_eigenLattice E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE c hc e he
  | zero => simp
  | add c d _ _ hc hd =>
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact add_mem (hc e he) (hd e he)
  | smul s c _ hc =>
    have h1 : ∑ a, τE ((s • c) a) • MP a e = ∑ a, τE (c a) • MP a ((τ s : K) • e) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : τE ((s • c) a) = (τ s : K) * τE (c a) := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        exact congrArg (· * τE (c a)) (hτE s)
      rw [h2, mul_smul, (MP a).map_smul, smul_comm]
    rw [h1]
    exact hc _ (by simpa [algebraMap_smul] using (FP.eigLat (X.A true).t.act τ).smul_mem (τ s) he)

end GlobalTheory.FlatCM.HomLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefiniteStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  first | exact @GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | exact GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | (intros; apply GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan <;> assumption)
end

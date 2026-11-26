module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.WeilSqKer

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  intro S A _ _ hA P hP h₁ h₂ hsym hamp k _ _ x₀ m hm a b ha hb ha2 c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hA hD hamp hD
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hS : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
    (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsw : ∀ (T : Over S) (x y : T ⟶ A), pc hP x y = pc hP y x := fun T x y => by
    have h := congrArg (pull (lift x y).left) hS
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst] at h
    exact h
  let T : Over S := Over.mk x₀
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl

  have hpt : ∀ {N : LB T.left} (hN : N.IsLB), cls N hN = 0 := fun {N} hN => by
    haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨i, hi⟩ := exists_chart hN p
    exact (cls_eq_zero_iff hN).2
      (DescendedPrincipal.exists_gen_of_chart hN i fun y => Subsingleton.elim p y ▸ hi)
  have haa : pc hP (fst T A ≫ a) (fst T A ≫ a) = 0 := by
    unfold pc
    rw [← comp_lift, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      hpt (pull_isLB hP _), map_zero]
  have ha2' : pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A) = 0 := by
    rw [← hB]
    obtain ⟨u, hu⟩ := ha2
    have z := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨u, hu⟩
    rw [cls_pull hP] at z
    have z' := congrArg (pull (β_ T A).hom.left) z
    rw [← pull_comp, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst, map_zero] at z'
    unfold pc
    rw [← MonObj.comp_mul, ← pow_two]
    exact z'
  obtain ⟨φ, hφ⟩ : ∃ φ : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a), φ.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T A).left _ + (-1 : ℤ) • pull ((fst T A ≫ a) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB', hsw _ (snd T A) (fst T A ≫ a), haa]
    calc _ = -(pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A)) := by abel
      _ = 0 := by rw [ha2', neg_zero]
  have h1 : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a 1 1 :=
    DescendedPrincipal.weilIs_one_right hG hA hD fun p => by
      obtain ⟨θ, hθ⟩ := CommutatorPairing.exists_pull hD (⟨a, φ, hφ⟩ : Out.ThetaGrp A _ 1 T)
        (Out.overResι (⊤ : T.left.Opens))
      exact ⟨⊤, trivial, θ, hθ⟩
  have h1' := CommPairing.weilIs_symm hD h1
  have hc' := CommPairing.weilIs_symm hD hc
  rw [inv_one, ← hb] at h1'
  have hc'' : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) ((1 : ℤ) * (m : ℕ)) b a c⁻¹ := by
    rw [_root_.one_mul]; exact hc'
  have key := PairingLevels.weilIs_value_eq hG hA hD ht hc'' h1'
  exact inv_eq_one.1 key

end GlobalTheory.WeilSqKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  first | (exact @GlobalTheory.WeilSqKer.weilIs_eq_one) | (exact GlobalTheory.WeilSqKer.weilIs_eq_one) | (intros; apply GlobalTheory.WeilSqKer.weilIs_eq_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}
  {s : S ⟶ Sp R}

theorem act_zero_eq_one_wvs (o : Obj b N s) : o.act.act 0 = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ptModuleWvs (o : Obj b N s) (T : Over S) : Module (𝓞 D.F) (Additive (T ⟶ o.A)) where
  smul a g := Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
  one_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
    rw [map_one, o.act.one, Category.comp_id]; rfl
  mul_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
    rw [map_mul, o.act.mul, Category.assoc]
  smul_zero a := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((1 : T ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) = Additive.ofMul 1
    rw [one_comp]
  smul_add a g h := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((g.toMul * h.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (h.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)))
    rw [mul_comp]
  add_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
    rw [map_add (f := _), o.act.add, comp_mul]
  zero_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
    rw [map_zero, act_zero_eq_one_wvs, comp_one]

attribute [local instance] ptModuleWvs

def kerWSubWvs (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (hl : ∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a))
    (w : Ideal (𝓞 D.F)) (T : Over S) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ≫ ψ = 1 ∧ KilledBy o w g.toMul}
  zero_mem' := by
    refine ⟨one_comp ψ, fun a _ => ?_⟩
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    exact one_comp _
  add_mem' {g h} hg hh := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul * h.toMul) ≫ ψ = 1
      rw [mul_comp, hg.1, hh.1, _root_.mul_one]
    · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg.2 a ha, hh.2 a ha, _root_.mul_one]
  smul_mem' c g hg := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ ψ = 1
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, hl, ← Category.assoc, hg.1, one_comp]
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg.2 a ha,
        one_comp]

theorem card_kerW_eq_pow : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {S : Scheme.{0}} {N : ℕ} {s : S ⟶ Sp R} (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ →
    (∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a)) →
    ∀ (w : Ideal (𝓞 D.F)), w.IsMaximal → ∀ {k : Type} [Field k] (y : Sp k ⟶ S),
    Finite {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} →
    ∃ j' : ℕ, Nat.card {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ j' := by
  intro p _ D R _ b S N s o o' ψ hψ hl w hw k _ y hfin
  haveI := hψ
  let K := kerWSubWvs o o' ψ hl w (Over.mk y)
  let e : K ≃ {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} :=
    { toFun := fun x => ⟨x.1.toMul, x.2⟩
      invFun := fun g => ⟨Additive.ofMul g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite K := Finite.of_equiv _ e.symm
  have htor : Module.IsTorsionBySet (𝓞 D.F) K (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show Additive.ofMul (x.1.toMul ≫ o.act.act (algebraMap _ _ a.1)) = Additive.ofMul 1
    rw [x.2.2 a.1 a.2]
  letI := Ideal.Quotient.field w
  letI : Module (𝓞 D.F ⧸ w) K := htor.module
  have hne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  haveI : Finite (𝓞 D.F ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hne
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  letI := Fintype.ofFinite K
  refine ⟨Module.finrank (𝓞 D.F ⧸ w) K, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w),
    Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.VarFlag

section Tri

variable {ι : Type} {m : ι → ℕ}

theorem par_map {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) {M : Mat m R} (hu : ∀ τ, IsUnit (M τ).det)
    (hl : ∀ τ i k, i < k → M τ i k = 0) : Par m ⊤ (M.map ψ) := fun τ => by
  refine ⟨fun _ _ => trivial, ?_, trivial, fun i j _ hij => ?_⟩
  · show (ψ.mapMatrix (M τ)).det ≠ 0
    rw [← RingHom.map_det]
    exact ((hu τ).map ψ).ne_zero
  · show ψ (M τ i j) = 0
    rw [hl τ i j hij, map_zero]

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem carries_at_image {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p g) :
    ∃ (φ₀ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))
      (g₀ : EigFrame Z φ₀ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
      g₀.Tri (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t ∧
      g₀.Tri (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g t' := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, h2, h3⟩ := hc
  have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
    have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
      (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp
        (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫
          spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hρ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ stalkPt C.Y y =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hx₀ : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ (stalkPt C.Y y ≫ C.π ≫ genι Z) =
      stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  refine ⟨(C.Y.X.presheaf.stalkSpecializes hsp).hom.comp φ₁, ?_⟩
  let g₀ := Classical.choose (ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀)
  have hg₀ := Classical.choose_spec (ValCoord.exists_bc f (C.Y.X.presheaf.stalkSpecializes hsp).hom hx₀)
  exact ⟨g₀, t, t', ValCoord.tri_bc hx₀ hg₀ (by rw [← CarriesAt.algebraMap_eq_comp_specializes hsp]; exact h2),
    ValCoord.tri_bc hx₀ hg₀ (by rw [← hψ]; exact h3)⟩

theorem tri_of_carries {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Z φ x} {g' : EigFrame Z φ' x}
    (hg : C.Carries p g) (hg' : C.Carries p g') : ∃ t, g.Tri (RingHom.id K) g' t := by
  obtain ⟨φ₀, g₀, t, s, T1, T2⟩ := carries_at_image C hg
  obtain ⟨φ₀', g₀', t₂, s₂, T1', T2'⟩ := carries_at_image C hg'
  have hinj : Function.Injective
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) :=
    IsFractionRing.injective _ _
  obtain rfl : φ₀' = φ₀ := RingHom.ext fun a =>
    hinj ((RingHom.congr_fun T1'.2.1 a).symm.trans (RingHom.congr_fun T1.2.1 a))
  have hφ : φ' = φ := T2'.2.1.trans T2.2.1.symm
  obtain ⟨T, hT, hTd, hTl⟩ := (g₀.tri_iff (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t).1 T1
  obtain ⟨T₂, hT₂, hT₂d, hT₂l⟩ := (g₀'.tri_iff (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 t₂).1 T1'
  obtain ⟨h, hh, hhd, hhl⟩ := (g₀.tri_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g s).1 T2
  obtain ⟨h₂, hh₂, hh₂d, hh₂l⟩ := (g₀'.tri_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g' s₂).1 T2'
  have hS₀ : g₀.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g₀ inferInstance
  have hid : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (RingHom.id _) ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp]

  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ (RingHom.id _)
    inferInstance hS₀ hid (RingHom.id_comp _).symm).1 g₀'
  have hMd := hMu M hM

  have hc1 : g₀.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0
      (T₂ * M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ C.f0 (RingHom.id _)
      (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) M T₂ inferInstance hM hT₂
    rwa [RingHom.comp_id] at this
  have heq := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hT.1 hT.2.1).1
    C.f0).1).unique hT hc1
  have hPT : Par Dw.mult ⊤ T := CarriesAt.par_of_tri (fun τ i => by rw [hTd]; exact Units.ne_zero _) hTl
  have hPT₂ : Par Dw.mult ⊤ T₂ := CarriesAt.par_of_tri (fun τ i => by rw [hT₂d]; exact Units.ne_zero _) hT₂l
  have hPM : Par Dw.mult ⊤
      (M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
    have e : M.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) =
        T₂⁻¹ * T := by
      rw [heq, ← mul_assoc, Mat.inv_mul hPT₂.det_ne, one_mul]
    rw [e]
    exact hPT₂.inv.mul hPT
  have hMl : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hik => by
    have h0 := (hPM τ).2.2.2 i k i.2 hik
    exact hinj (by rw [map_zero]; exact h0)

  have hSg : g.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ g inferInstance
  have hidK : x = spMap (RingHom.id K) ≫ x := by
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨N, hN, -⟩, -⟩ := (EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g _ φ' _ (RingHom.id K)
    inferInstance hSg hidK (by rw [RingHom.id_comp]; exact hφ)).1 g'
  have c1 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (N * h.map (RingHom.id K)) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g _ _ _ g'
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom (RingHom.id K) h N inferInstance hh hN
    rwa [RingHom.id_comp] at this
  have c2 : g₀.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g'
      (h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ g₀' _ _ _ g' (RingHom.id _)
      (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom M h₂ inferInstance hM hh₂
    rwa [RingHom.comp_id] at this
  have heqK := (((EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ g₀ _ _ _ _ inferInstance hS₀ hh₂.1 hh₂.2.1).1
    g').1).unique c1 c2
  have hmid : h.map (RingHom.id K) = h := funext fun τ => by ext i j; rfl
  rw [hmid] at heqK
  have hPh : Par Dw.mult ⊤ h := CarriesAt.par_of_tri (fun τ i => by rw [hhd]; exact Units.ne_zero _) hhl
  have hPh₂ : Par Dw.mult ⊤ h₂ := CarriesAt.par_of_tri (fun τ i => by rw [hh₂d]; exact Units.ne_zero _) hh₂l
  have hPMK := par_map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom hMd hMl
  have hNe : N = h₂ * M.map (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom * h⁻¹ := by
    rw [← heqK, mul_assoc, Mat.mul_inv hPh.det_ne, mul_one]
  have hPN : Par Dw.mult ⊤ N := by
    rw [hNe]
    exact (hPh₂.mul hPMK).mul hPh.inv
  exact ⟨fun τ i => Units.mk0 _ (CarriesAt.Par.diag_ne hPN τ i),
    (g.tri_iff _ g' _).2 ⟨N, hN, fun _ _ => rfl, fun τ i k hik => (hPN τ).2.2.2 i k i.2 hik⟩⟩

theorem carriesTri : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)},
    ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  intro E _ _ _ H Dw l Xo c Y C K _ φ φ' x p g g' hg hg'
  exact tri_of_carries C hg hg'

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundlePointFramesTriangular_component : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  first | exact @GlobalTheory.VarFlag.carriesTri | exact GlobalTheory.VarFlag.carriesTri | (intros; apply GlobalTheory.VarFlag.carriesTri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRing
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames ev ev_appLE ev_res ev_congr le_preimage_comp le_preimage_mono vec actR_vec
  spMap_ev_top ev_appTop eigLie vec_mem_eigLie initSpan)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.CompHS (flagOpen dense_flagOpen opensRange_inc)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

def cstF (X : FlagCover Y) (V : X.YY.Opens) (r : c.F) : Γ(X.YY, V) :=
  resG X.YY (le_top : V ≤ ⊤) ((X.π ≫ Y.s).appTop.hom (toΓ c.F r))

theorem ev_cstF (X : FlagCover Y) {S : Type} [CommRing S] (w : Sp S ⟶ X.YY) (V : X.YY.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ V)
    (ψ : c.F →+* S) (hψ : w ≫ X.π ≫ Y.s = spMap ψ) (r : c.F) : ev w V hw (cstF X V r) = ψ r := by
  unfold cstF
  rw [ev_res w le_top hw le_top, ev_appTop]
  have key : (ev (w ≫ X.π ≫ Y.s) ⊤ le_top).comp (toΓ c.F) = ψ := by
    have : spMap ((ev (w ≫ X.π ≫ Y.s) ⊤ le_top).comp (toΓ c.F)) = spMap ψ := (spMap_ev_top _).trans hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  exact RingHom.congr_fun key r

def eigDefect (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E)
    (j : Fin (X.F.M k).n) : Γ(X.YY, X.F.U k) :=
  ∑ m, (X.π.appLE (X.F.M k).U (X.F.U k) (X.F.le k)).hom ((X.F.M k).ρ a j m) * X.F.u k σ m i -
    cstF X (X.F.U k) (embK c σ a) * X.F.u k σ j i

theorem ev_eigDefect (X : FlagCover Y) {S : Type} [CommRing S] (w : Sp S ⟶ X.YY) (k : X.F.J)
    (hw : ⊤ ≤ w ⁻¹ᵁ X.F.U k) (ψ : c.F →+* S) (hψ : w ≫ X.π ≫ Y.s = spMap ψ) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (a : 𝓞 E) (j : Fin (X.F.M k).n) :
    ev w _ hw (eigDefect X k σ i a j) =
      (((X.F.M k).ρ a).map (ev (w ≫ X.π) (X.F.M k).U (X.F.inM hw rfl))).mulVec
        (fun m => X.F.uAt k w hw σ m i) j - ψ (embK c σ a) * X.F.uAt k w hw σ j i := by
  unfold eigDefect
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_mul, ev_cstF X w _ hw ψ hψ]
  simp only [map_mul, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_appLE w X.π (X.F.le k) hw (X.F.inM hw rfl)]
  rfl

theorem eigDefect_eq_zero (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E)
    (j : Fin (X.F.M k).n) : eigDefect X k σ i a j = 0 := by
  refine GlobalTheory.DRFlag.AdaptedOfStep.eq_zero_of_dense (dense_flagOpen X) _ fun K _ w hw hwD => ?_
  obtain ⟨ψ, hψ⟩ : ∃ ψ : c.F →+* K, spMap ψ = w ≫ X.π ≫ Y.s := ⟨_, spMap_ev_top _⟩
  letI : Algebra c.F K := ψ.toAlgebra
  have hall : ⊤ ≤ w ⁻¹ᵁ flagOpen X := ((IsLocalRing.closed_point_mem_iff (U := w ⁻¹ᵁ flagOpen X)).1 hwD).ge
  have hr : Set.range w ⊆ Set.range X.inc := by
    rintro _ ⟨p, rfl⟩
    have : w p ∈ flagOpen X := hall (Set.mem_univ p)
    rw [← opensRange_inc X] at this
    exact this
  let w' : Sp K ⟶ X.Yo := IsOpenImmersion.lift X.inc w hr
  have hw' : w' ≫ X.inc = w := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, hyd⟩ : ∃ y : Sp K ⟶ Xo.XF c, y = w' ≫ pullback.snd X.π Y.j := ⟨_, rfl⟩
  have hx : w ≫ X.π = y ≫ Y.j := by
    rw [← hw', hyd, Category.assoc, Category.assoc, pullback.condition]
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    have e1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    calc y ≫ pullback.snd _ _ = (w ≫ X.π) ≫ Y.s := by rw [hx, Category.assoc, e1]
      _ = spMap ψ := by rw [Category.assoc, hψ]
  have htop := X.top K y hy w hx k hw σ
  have hmem : X.F.vecAt k w hw hx σ i ∈ eigLie c (y ≫ Y.j) σ := by
    rw [← htop]; exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have heig := (vec_mem_eigLie (X.F.M k).toMChart (y ≫ Y.j) (X.F.inM hw hx) σ
    (fun m => X.F.uAt k w hw σ m i)).1 hmem a
  rw [ev_eigDefect X w k hw ψ hψ.symm, ev_congr hx _ _ (X.F.inM hw hx), heig]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact sub_self _

theorem actR_vecAt (X : FlagCover Y) {R : Type} [CommRing R] (φ : c.F →+* R) (z : Sp R ⟶ X.YY) (k : X.F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hφ : z ≫ X.π ≫ Y.s = spMap φ) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (a : 𝓞 E) :
    actR Y.t.act a (X.F.vecAt k z hz rfl σ i) = φ (embK c σ a) • X.F.vecAt k z hz rfl σ i := by
  show actR Y.t.act a (vec _ _ _ _) = φ (embK c σ a) • vec _ _ _ _
  rw [actR_vec, ← map_smul]
  congr 1
  funext j
  have h := ev_eigDefect X z k hz φ hφ σ i a j
  rw [eigDefect_eq_zero, map_zero] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact sub_eq_zero.1 h.symm

theorem existsUnique_of_retraction {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ}
    (v e : Fin m → N) (ρ : N →ₗ[R] Fin m → R) (hρ : ∀ i, ρ (v i) = Pi.single i 1) (P : N → Prop)
    (hv : ∀ i, P (v i)) (he : ∀ w, P w → ∃! a : Fin m → R, w = ∑ k, a k • e k) (hli : LinearIndependent R v)
    (w : N) (hw : P w) : ∃! a : Fin m → R, w = ∑ i, a i • v i := by
  classical
  choose A hA _ using fun i => he (v i) (hv i)
  let C : Matrix (Fin m) (Fin m) R := Matrix.of fun k i => ρ (e k) i
  have hAC : Matrix.of A * C = 1 := by
    ext i j
    have h := congrFun (congrArg ρ (hA i)) j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hρ, map_sum] at h
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine Eq.trans ?_ (h.symm.trans ?_)
    · rfl
    · rw [Pi.single_apply]; simp only [eq_comm]
  have hCA : C * Matrix.of A = 1 := mul_eq_one_comm.1 hAC
  have hek : ∀ k, e k = ∑ i, C k i • v i := fun k => by
    simp only [hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have : ∀ j, (∑ i, C k i * A i j) = (1 : Matrix (Fin m) (Fin m) R) k j := fun j => by
      rw [← hCA, Matrix.mul_apply]; rfl
    simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  obtain ⟨b, hb, -⟩ := he w hw
  have hex : w = ∑ i, (∑ k, b k * C k i) • v i := by
    rw [hb]
    simp only [Finset.sum_smul, ← smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [hek k, Finset.smul_sum]
  refine ⟨_, hex, fun a ha => funext fun i => ?_⟩
  exact (Fintype.linearIndependent_iffₛ.1 hli) _ _ (ha.symm.trans hex) i

theorem framesExist_flagCover (X : FlagCover Y) : FramesExist X := by
  intro R _ _ φ z k hz hφ
  have hf : Nonempty (GlobalTheory.ShFam.EigFrame Y φ (z ≫ X.π)) := by
    have hc : (z ≫ X.π) ≫ Y.s = spMap φ ≫ spMap (RingHom.id c.F) := by
      rw [Category.assoc, hφ]
      exact ((congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)).symm
    have h := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y R φ (pullback.lift _ _ hc)
      (pullback.lift_snd _ _ _)
    rwa [pullback.lift_fst] at h
  obtain ⟨f⟩ := hf
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun σ i => X.F.vecAt k z hz rfl σ i)
    (fun σ i a => actR_vecAt X φ z k hz hφ σ i a) (fun σ w hw => ?_), fun σ i => rfl⟩
  obtain ⟨W, hW⟩ := X.F.uAt_split k z hz σ
  refine existsUnique_of_retraction (fun i => X.F.vecAt k z hz rfl σ i) (f.vec σ)
    ((Matrix.mulVecLin W).comp (vec (X.F.M k).toMChart (z ≫ X.π) (X.F.inM hz rfl)).symm.toLinearMap)
    (fun i => ?_) (fun u => ∀ a, actR Y.t.act a u = φ (embK c σ a) • u)
    (fun i a => actR_vecAt X φ z k hz hφ σ i a) (fun u hu => f.existsUnique_sum σ u hu)
    (X.F.linearIndependent_vecAt k z hz rfl σ) w hw
  show W.mulVec ((vec _ _ _).symm (vec _ _ _ _)) = _
  rw [LinearEquiv.symm_apply_apply]
  funext r
  have := congrFun (congrFun hW r) i
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [Matrix.mulVec, dotProduct, this, Pi.single_apply]

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagChartFrames_eigenFrames_localRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X := by
  first | exact @GlobalTheory.VarFlag.framesExist_flagCover | exact GlobalTheory.VarFlag.framesExist_flagCover | (intros; apply GlobalTheory.VarFlag.framesExist_flagCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRing
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlagSpec

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt stalkPt genericPt constF)
open GlobalTheory.VarFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)

theorem sp_comp_sp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ψ : S →+* T) (φ : R →+* S) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem eq_spMap_of_comp {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {ι : R →+* R'}
    (hι : Function.Injective ι) {h : Sp R ⟶ Sp S} {φ : S →+* R} (e : spMap ι ≫ h = spMap (ι.comp φ)) :
    h = spMap φ := by
  obtain ⟨p, rfl⟩ := Spec.map_surjective h
  have h1 : ι.comp p.hom = ι.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← e, ← sp_comp_sp]; rfl
  have hp : p.hom = φ := RingHom.ext fun a => hι (RingHom.congr_fun h1 a)
  rw [← hp]; rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genericPt_genStr {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    {e : F ≃+* c.F} (C : FlagCpt Z e) :
    genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genStr Z = spMap (constF e C.Y) := by
  letI := (constF e C.Y).toAlgebra
  rw [← Category.assoc, ← C.y0_x, Category.assoc, GlobalTheory.Toroidal.genStr, Z.jQ_over]
  exact GlobalTheory.ShFam.ptF_snd _

theorem flagSpaceComponent_stalkPoint_over_coefficientField {Y : Model Xo c (RingHom.id c.F)} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Y e) (y : C.Y.X)
    {φ : c.F →+* C.Y.X.presheaf.stalk y} {f : EigFrame Y φ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t) :
    stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y ≫ Y.s = spMap φ := by
  have hg : GlobalTheory.Toroidal.genι Y ≫ Y.s = GlobalTheory.Toroidal.genStr Y := by
    rw [GlobalTheory.Toroidal.genι, GlobalTheory.Toroidal.genStr, pullback.condition]
    exact (congrArg (pullback.snd Y.s (spMap (RingHom.id c.F)) ≫ ·) (spMap_id' _)).trans (Category.comp_id _)
  refine eq_spMap_of_comp (IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField) ?_
  rw [← h.2.1, ← genericPt_genStr C, ← hg]
  have h1 := congrArg (· ≫ Y.s) h.1
  simp only [Category.assoc] at h1
  exact h1.symm

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isFrameAt_map {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {z : Sp R ⟶ Z} {k : F.J} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k}
    {g : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g) (ψ : R →+* R') {φ' : c.F →+* R'}
    {g' : EigFrame Y φ' ((spMap ψ ≫ z) ≫ π)} (hg' : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v g embτ basisIdx) ψ g') :
    IsFrameAt F (spMap ψ ≫ z) k (GlobalTheory.FlagMod.le_preimage_comp _ hz) g' := by
  intro σ i
  rw [hg' σ i, hg σ i, ← GlobalTheory.FlagMod.tanPull_left ψ (Category.assoc _ _ _).symm,
    F.tanPull_vecAt k ψ z hz _ rfl rfl]

theorem co_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R : Type} [CommRing R] {φ : c.F →+* R} (z : Sp R ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') {g g' : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') (τ : E →+* ℂ) :
    (g.co g' τ).BlockTriangular id ∧ ∀ i, IsUnit (g.co g' τ i i) := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have e : g.co g' τ = (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) := by
    refine GlobalTheory.ShFam.EigFrame.co_eq fun i => ?_
    rw [funext (hg τ), hg' τ i, GlobalTheory.LieMet.isComb_iff]
    exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i
  rw [e]
  exact ⟨F.B_map_tri k k' τ _, fun i => (F.isUnit_B_diag k k' τ i).map (GlobalTheory.FlagMod.ev z _ hh)⟩

end GlobalTheory.VarFlagSpec


open GlobalTheory.VarFlagSpec GlobalTheory.ShFam in
theorem GlobalTheory.VarFlag.rel_specialise : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y),
    GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C →
    ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X),
    u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y →
    GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) →
    GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C hCT A _ _ _ u v huv hL
  set ι := algebraMap A (FractionRing A) with hι_def
  have hι : Function.Injective ι := IsFractionRing.injective A (FractionRing A)
  set ρ := IsLocalRing.residue A with hρ_def

  set y := v (IsLocalRing.closedPoint A) with hy_def
  let ψA : C.Y.X.presheaf.stalk y →+* A := (Scheme.stalkClosedPointTo v).hom
  have hv : v = spMap ψA ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk v).symm
  obtain ⟨φ₁, f, t, hf0, -⟩ := C.gr_spec y
  have hxA : u ≫ X.π = spMap ψA ≫ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) := by
    rw [huv, hv, Category.assoc]
  have hsA : u ≫ X.π ≫ Y.s = spMap (ψA.comp φ₁) := by
    rw [← Category.assoc, hxA]
    simp only [Category.assoc]
    rw [flagSpaceComponent_stalkPoint_over_coefficientField C y hf0, sp_comp_sp]

  obtain ⟨kk, hkk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover u
  obtain ⟨gA, hgA⟩ := hFE A (ψA.comp φ₁) u kk hkk hsA
  obtain ⟨fA, hfA⟩ := f.exists_isMap ψA (φ' := ψA.comp φ₁) (x' := u ≫ X.π) rfl hxA

  obtain ⟨φL, k0, hz0, gL, hsL, hgL, hcL⟩ := hL
  obtain rfl : φL = ι.comp (ψA.comp φ₁) := GlobalTheory.ShFam.EigLoc.spMap_inj (by
    rw [← hsL, Category.assoc, hsA, sp_comp_sp])
  have hxL : (spMap ι ≫ u) ≫ X.π = spMap ι ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fL, hfL⟩ := fA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  obtain ⟨gL', hgL'⟩ := gA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  have hgL'fr := isFrameAt_map X.F hgA ι hgL'
  have hfLf : f.IsMap (ι.comp ψA) fL := fun τ i => by
    rw [hfL τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hcF : C.Carries (spMap ι ≫ v) fL :=
    ⟨y, ι.comp ψA, φ₁, f, t, 1, by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      hfLf.tri rfl (by rw [hxL, hxA, ← Category.assoc, sp_comp_sp])⟩
  obtain ⟨t1, ht1⟩ := hCT (FractionRing A) _ _ _ _ fL gL hcF hcL
  have hfLid : fL.IsMap (RingHom.id _) fL := fun τ i => by rw [VarFlagSpec.spMap_dualMap_id, Category.id_comp]

  have key : ∀ τ, (fA.co gA τ).BlockTriangular id ∧ ∀ i, IsUnit (fA.co gA τ i i) := by
    intro τ
    have h1 := ht1.co τ hfLid
    have h2 := co_of_isFrameAt X.F _ k0 kk hz0 _ hgL hgL'fr τ
    have hm : fL.co gL' τ = (fA.co gA τ).map ι := hfL.co τ hgL' hxL
    have hT1 : (fL.co gL τ).BlockTriangular id := fun a i h => h1.1 a i h
    have htri : (fL.co gL' τ).BlockTriangular id := by
      rw [← fL.co_mul gL gL' τ]; exact hT1.mul h2.1
    have hMt : (fA.co gA τ).BlockTriangular id := fun a i h => hι (by
      have := htri h
      rw [hm, Matrix.map_apply] at this
      rw [this, map_zero])
    refine ⟨hMt, fun i => ?_⟩
    have hdet := fA.isUnit_det_co gA τ
    rw [Matrix.det_of_upperTriangular hMt] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => fA.co gA τ j j) (Finset.mem_univ i)) hdet

  have hxk : (spMap ρ ≫ u) ≫ X.π = spMap ρ ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fk, hfk⟩ := fA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  obtain ⟨gk, hgk⟩ := gA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  have hfkf : f.IsMap (ρ.comp ψA) fk := fun τ i => by
    rw [hfk τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hmk : ∀ τ, fk.co gk τ = (fA.co gA τ).map ρ := fun τ => hfk.co τ hgk hxk
  refine ⟨ρ.comp (ψA.comp φ₁), kk, GlobalTheory.FlagMod.le_preimage_comp _ hkk, gk, ?_, isFrameAt_map X.F hgA ρ hgk, ?_⟩
  · rw [Category.assoc, hsA, sp_comp_sp]
  · refine ⟨y, ρ.comp ψA, φ₁, f, t, fun τ i => (((key τ).2 i).map ρ).unit,
      by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      by rw [hxk, hxA, ← Category.assoc, sp_comp_sp], rfl, fun τ i => ⟨fun a => fk.co gk τ a i, ?_, ?_, ?_⟩⟩
    · rw [hmk]; beta_reduce; rw [Matrix.map_apply, IsUnit.unit_spec]
    · intro a ha
      rw [hmk]; beta_reduce; rw [Matrix.map_apply, (key τ).1 ha, map_zero]
    · rw [← funext (hfkf τ)]
      exact fk.co_spec gk τ i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X), u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y → GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  first | exact @GlobalTheory.VarFlag.rel_specialise | exact GlobalTheory.VarFlag.rel_specialise | (intros; apply GlobalTheory.VarFlag.rel_specialise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PicGenericInj

theorem exists_gen_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ N : LB G.left, N.IsLB → (∃ t : LB.Gen (N.pull (pullback.fst G.hom (jK R))), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ _ _ _ G _ hG N hN ht
  have := hG.smooth
  have := hG.geomConnected
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  exact GenericExtend.exists_isGen_of_densePart _ _ (jK R) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    h₃ inferInstance G (eSec G) N (Over.w η[G]) ‹_› (geometricallyIntegral_of_smooth G.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ht

end GlobalTheory.PicGenericInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

variable {X Y : Scheme.{0}}

def evU {Z : Scheme.{0}} (g : Z ⟶ X) {W : X.Opens} (hg : ∀ z, g z ∈ W) (f : Γ(X, W)ˣ) : Γ(Z, ⊤)ˣ :=
  res (fun z _ => hg z : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ W) (pullU g W f)

def rat (π : X ⟶ Y) {V W : Y.Opens} (f : Γ(X, π ⁻¹ᵁ V)ˣ) (g : Γ(X, π ⁻¹ᵁ W)ˣ) :
    Γ(X, π ⁻¹ᵁ (V ⊓ W))ˣ :=
  res (π.preimage_mono inf_le_left) f * (res (π.preimage_mono inf_le_right) g)⁻¹

def Chart (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) : Type :=
  {p : (V : Y.Opens) × Γ(X, π ⁻¹ᵁ V)ˣ // E p.1 p.2}


open Classical in
def trans (π : X ⟶ Y) (E : ∀ V : Y.Opens, Γ(X, π ⁻¹ᵁ V)ˣ → Prop) (i j : Chart π E) :
    Γ(Y, i.1.1 ⊓ j.1.1)ˣ :=
  if h : ∃ u, pullU π _ u = rat π i.1.2 j.1.2 then h.choose else 1

section Eigen

variable {K : Type} [Field K] {A A' T : Over (Sp K)} [GrpObj A] [GrpObj A']

end Eigen

end GlobalTheory.EigenDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.FiniteOverProj

theorem isProjOver_of_isFinite_over :
    ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  intro A o _ _ κ M Z z π s hz hπ _ hs
  have h : IsProjOver (π ≫ z) := GlobalTheory.isProjOver_comp_of_isFinite π hz
  rw [← hs] at h
  exact GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap κ h

end GlobalTheory.FiniteOverProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_of_isFinite_over_projective : ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  first | exact @GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over | exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over | (intros; apply GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem isPullback_whiskerLeft_snd_left {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) :
    IsPullback (A ◁ j).left (snd A B').left (snd A B).left j.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.hom B.hom) (v₁₃ := A.hom) (h₂₂ := B.hom)
    ?_ ?_ (IsPullback.of_hasPullback A.hom B.hom)
  · have hw : j.left ≫ B.hom = B'.hom := Over.w j
    rw [Over.whiskerLeft_left_fst, hw]
    exact IsPullback.of_hasPullback A.hom B'.hom
  · simp

theorem isOpenImmersion_whiskerLeft_left_and_range {S : Scheme.{0}} (A : Over S) {B' B : Over S}
    (j : B' ⟶ B) [IsOpenImmersion j.left] :
    IsOpenImmersion (A ◁ j).left ∧
      Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  have h := isPullback_whiskerLeft_snd_left A j
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h.flip
    inferInstance, ?_⟩
  simpa [Set.image_univ] using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ

end GlobalTheory.DualCon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSndStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd : ∀ {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) [IsOpenImmersion j.left], IsOpenImmersion (A ◁ j).left ∧ Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  first | exact @GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | exact GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | (intros; apply GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range <;> assumption)
end
end

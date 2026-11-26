module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
section -- merged from Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH

namespace TorusFibre
variable {k : Type} [Field k]

end TorusFibre

namespace AbelianFibre
variable {k : Type} [Field k]

theorem lbIso_of_gens {X : Scheme.{0}} {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) :
    LBIso A B := by
  refine ⟨⟨fun p => res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹⟩,
    fun (p q : B.ι × A.ι) => unit_ext fun y hy => by
      have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
          (res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹) =
          gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
        rw [map_mul, map_inv, gm_res (𝟙 X) y _ hp, gm_res (𝟙 X) y _ hp]
      have e₁ := congrArg (gm (𝟙 X) y _) (hs p.2 q.2)
      have e₂ := congrArg (gm (𝟙 X) y _) (ht p.1 q.1)
      have m₁ : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
      have m₂ : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
      rw [map_mul, gm_res (𝟙 X) y _ m₁, gm_res (𝟙 X) y _ m₁] at e₁
      rw [map_mul, gm_res (𝟙 X) y _ m₂, gm_res (𝟙 X) y _ m₂] at e₂
      refine ((gm_res (𝟙 X) y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
        (gm_div A B (𝟙 X) y p q hy) ((gm_res (𝟙 X) y _ hy _).trans (v q hy.2))).trans ?_)))
      rw [e₁, e₂, mul_inv]
      exact mul_mul_mul_comm _ _ _ _⟩

end AbelianFibre

namespace MonomialImmersion
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

end MonomialImmersion

end GlobalTheory.ZH
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagSqAxes

theorem lift_mul_lift₂ {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem weilIs_one_of_gen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) {N : ℕ} {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : Out.WeilIs A L N x y 1 := by
  have hG := GlobalTheory.globalFns_holds
  have hM : (GlobalTheory.UU.trivRig A).L.IsLB := Out.Inh.trivLB_isLB _
  have h1 : Out.WeilIs A (GlobalTheory.UU.trivRig A).L N (x ≫ 𝟙 A) (y ≫ 𝟙 A) 1 := by
    rw [Category.comp_id, Category.comp_id]
    exact (GlobalTheory.UU.cubWeil_iff_weilIs (c := GlobalTheory.UU.trivCub A) hG hA hx hy 1).1 (GlobalTheory.UU.cubWeil_triv hx hy)
  have hw : LBIso (lbPow L 1) ((GlobalTheory.UU.trivRig A).L.pull (Over.Hom.left (𝟙 A))) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hM _) (GlobalTheory.lbIso_lbPow_one hL)
      (GlobalTheory.ZH.AbelianFibre.lbIso_of_gens t ht (GlobalTheory.UU.unitGen _ _) (GlobalTheory.UU.unitGen_isGen _ _))
  have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hM (𝟙 A) hw h1
  simp only [Nat.cast_one, _root_.mul_one] at h2
  exact h2

theorem weilIs_axis {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB B.left} (hP : P.IsLB) (ψ : A ⟶ B) [IsMonHom ψ]
    (ht : ∃ t : (P.pull ψ.left).Gen, t.IsGen) (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ)
    (hN : 0 < N) (hNk : (N : κ) ≠ 0) (a b : Over.mk y ⟶ A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    Out.WeilIs B P N (a ≫ ψ) (b ≫ ψ) 1 := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := ht
  have hL : (P.pull ψ.left).IsLB := pull_isLB hP _
  have pa : (a ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have pb : (b ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hb, MonObj.one_comp]
  obtain ⟨c', hc'⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S B P hB hP κ y N hN hNk _ _ pa pb
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hP ψ (GlobalTheory.lbIso_lbPow_one hL) hc'
  simp only [Nat.cast_one, _root_.mul_one] at h1
  have h2 := weilIs_one_of_gen hA hL t ht ha hb
  rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2] at hc'

end GlobalTheory.DiagSqAxes

namespace GlobalTheory.DiagSqAxes

theorem weilIs_diag_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ), 0 < N → (N : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ N = 1 → b ^ N = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P N (lift a 1) (lift 1 b) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N a b (c ^ 2) := by
  intro S A _ _ hA P hP h₂ h₁ hsym κ _ _ y N hN hNk a b ha hb c hc
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have e11 : Out.WeilIs (G2 A) P N (lift a 1) (lift b 1) 1 := by
    have h := weilIs_axis hA hAA hP (lift (𝟙 A) (1 : A ⟶ A)) h₁ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e22 : Out.WeilIs (G2 A) P N (lift 1 a) (lift 1 b) 1 := by
    have h := weilIs_axis hA hAA hP (lift (1 : A ⟶ A) (𝟙 A)) h₂ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e21 : Out.WeilIs (G2 A) P N (lift 1 a) (lift b 1) c := by
    have hw : LBIso (lbPow P 1) (P.pull (lift (snd A A) (fst A A)).left) :=
      LBIso.trans (GlobalTheory.isLB_lbPow hP 1) hP (pull_isLB hP _) (GlobalTheory.lbIso_lbPow_one hP) hsym
    have h' : Out.WeilIs (G2 A) P N (lift 1 a ≫ lift (snd A A) (fst A A)) (lift b 1 ≫ lift (snd A A) (fst A A)) c := by
      simpa only [comp_lift, lift_fst, lift_snd] using hc
    have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP _ hw h'
    simp only [Nat.cast_one, _root_.mul_one] at h
    exact h
  have r1 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP e11 e21
  have r2 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc e22
  rw [lift_mul_lift₂] at r1 r2
  have s := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP (GlobalTheory.CommPairing.weilIs_symm hP r1)
    (GlobalTheory.CommPairing.weilIs_symm hP r2)
  have s' := GlobalTheory.CommPairing.weilIs_symm hP s
  rw [lift_mul_lift₂] at s'
  simp only [_root_.mul_one, _root_.one_mul] at s'
  have hd : Out.WeilIs (G2 A) P N (a ≫ lift (𝟙 A) (𝟙 A)) (b ≫ lift (𝟙 A) (𝟙 A)) (c ^ 2) := by
    simp only [comp_lift, Category.comp_id]
    convert s' using 1
    rw [← _root_.mul_inv, inv_inv, pow_two]
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hD hP (lift (𝟙 A) (𝟙 A)) (GlobalTheory.lbIso_lbPow_one hD) hd
  simp only [Nat.cast_one, _root_.mul_one] at h
  exact h

end GlobalTheory.DiagSqAxes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QuotFamRep

theorem spMap_rid (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

section Calc

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc

theorem exists_pull {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h k ζ s) (f : S' ⟶ S) : ∃ c' : SiegPre h k ζ (f ≫ s), SiegPB c' c f :=
  (GlobalTheory.T.siegelPre_pullback_principal_ringChange h k B B ζ ζ (RingHom.id B) S S' s (f ≫ s) f rfl (by rw [spMap_rid, Category.comp_id])).1 c

theorem asIdeal_eq_bot_iff {A A' : Type} [CommRing A] [CommRing A'] [IsDomain A] [IsDomain A'] (j : A →+* A')
    (hj : Function.Injective j) (hf : IsFinite (spMap j)) (y : Sp A') :
    ((spMap j) y).asIdeal = ⊥ ↔ y.asIdeal = ⊥ := by
  algebraize [j]
  have hm : Module.Finite A A' := by rw [IsFinite.SpecMap_iff] at hf; exact hf
  have : Algebra.IsIntegral A A' := inferInstance
  show Ideal.comap (algebraMap A A') y.asIdeal = ⊥ ↔ _
  refine ⟨fun e => Ideal.eq_bot_of_comap_eq_bot e, fun e => ?_⟩
  rw [e]; exact Ideal.comap_bot_of_injective (algebraMap A A') hj

end GlobalTheory.QuotFamRep

namespace GlobalTheory


open QuotFamRep in
theorem quotFam_represents : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  intro h n N F j Q hn hN hnN hj hjz hfin het hsurj S s' c hS hd hc
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega

  let S' := pullback s' (spMap j)
  let q : S' ⟶ S := pullback.fst s' (spMap j)
  let t : S' ⟶ Sp (cycAway N) := pullback.snd s' (spMap j)
  have hq := GlobalTheory.T.siegelPre_pullback_principal_ringChange h n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) S S' s' (t ≫ spMap j) q
    rfl (by rw [spMap_rid, Category.comp_id]; exact pullback.condition)
  obtain ⟨c', hc'⟩ := hq.1 c
  have hc'P : c'.Principal := hq.2.1 c c' hc' hc

  obtain ⟨S₁, π₁, C, hπf, hπe, hπs, hCrel, -⟩ := GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N (cycAway n) (cycAway N) (zetaAway n)
    (cycBase hN0) j S' t c' hn hN hnN (by rw [cycBase_ζ]; exact hjz) hc'P
  let p : S₁ ⟶ S := π₁ ≫ q
  have : IsFinite p := by dsimp [p, q]; infer_instance
  have : Etale p := by dsimp [p, q]; infer_instance
  have : Surjective p := by dsimp [p, q]; infer_instance
  have hp : p ≫ s' = (π₁ ≫ t) ≫ spMap j := by
    simp only [p, q, t, Category.assoc, pullback.condition]
  have hred : IsReduced S₁ := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hden : Dense {x : S₁ | ((π₁ ≫ t) x).asIdeal = ⊥} := by
    have : UniversallyOpen p := UniversallyOpen.of_flat p
    have e : ∀ x, s' (p x) = spMap j ((π₁ ≫ t) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply]
    convert hd.preimage p.isOpenMap using 1
    ext x
    show ((π₁ ≫ t) x).asIdeal = ⊥ ↔ (s' (p x)).asIdeal = ⊥
    rw [e, asIdeal_eq_bot_iff j hj hfin]
  have hCP : C.Principal := sRel_principal hCrel hc'P
  obtain ⟨f₁, hf₁s, hf₁⟩ := F.rep S₁ (π₁ ≫ t) C hred hden hCP

  obtain ⟨c₀, hC0, h0C⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j S₁ (π₁ ≫ t) C hN0
    (isUnit_natCast hN0) hnN hjz
  have hf₁N : SRel C F.univ (N / n) (N / n) f₁ := sRel_scale ((sRel_one_one_iff _ _ _).2 hf₁) _
  have h0F : SRel c₀ F.univ 1 (N / n) f₁ := by simpa using sRel_comp hf₁N h0C
  obtain ⟨g, hg⟩ : ∃ g : S₁ ⟶ Q.X, g = f₁ ≫ Q.π := ⟨_, rfl⟩
  have hgQ : SRel C Q.univ (N / n) 1 g := hg ▸ sRel_comp Q.low hf₁N
  have h0Q : SiegPB c₀ Q.univ g := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_comp hgQ h0C)
  have hCc : SRel C c (N / n) 1 p := sRel_comp ((sRel_one_one_iff _ _ _).2 hc') hCrel
  have h0c₁ : SRel c₀ c 1 1 p := by simpa using sRel_comp hCc h0C
  have hf₁p : f₁ ≫ F.s ≫ spMap j = p ≫ s' := by rw [← Category.assoc, hf₁s, hp]
  have hgs : g ≫ Q.s = p ≫ s' := by rw [hg, Category.assoc, Q.base]; exact hf₁p

  have key : pullback.fst p p ≫ g = pullback.snd p p ≫ g := by
    have : IsReduced (pullback p p) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst p p)
    have : IsSeparated Q.s := isSeparated_of_isQProjOver Q.qproj
    refine (GlobalTheory.hom_eq_iff_forall_isAlgClosed Q.s ?_).2 fun K _ _ x => ?_
    · simp only [Category.assoc, hgs, pullback.condition_assoc]
    obtain ⟨cx, hcx⟩ := exists_pull c₀ (x ≫ pullback.fst p p)
    have hx₁ := (sRel_one_one_iff _ _ _).2 hcx
    have hx₂ : SRel cx c₀ 1 1 (x ≫ pullback.snd p p) := by
      refine sRel_cancel h0c₁ ?_
      have := sRel_comp h0c₁ hx₁
      convert this using 1
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e := Q.fibre K (x ≫ pullback.fst p p ≫ f₁) (x ≫ pullback.snd p p ≫ f₁) _ cx
      (by simp only [Category.assoc, hf₁p, pullback.condition_assoc])
      (by simpa only [Category.assoc] using sRel_comp h0F hx₁)
      (by simpa only [Category.assoc] using sRel_comp h0F hx₂)
    simpa only [hg, Category.assoc] using e
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₁), g₁ ≫ p = g₂ ≫ p → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ e => by
    have := pullback.lift g₁ g₂ e ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : p ≫ EffectiveEpi.desc p g hcoeq = g := EffectiveEpi.fac p g hcoeq
  refine ⟨EffectiveEpi.desc p g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi p, ← Category.assoc, hfac, hgs]
  · exact GlobalTheory.T.siegPB_of_finite_etale_surjective_cover h n (cycAway n) (cycBase hn0) S S₁ Q.X s' ((π₁ ≫ t) ≫ spMap j) Q.s c c₀ Q.univ p _ hn
      (hN.of_dvd_nat hnN) Q.princ inferInstance inferInstance inferInstance ((sRel_one_one_iff _ _ _).1 h0c₁)
      (hfac.symm ▸ h0Q)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  first | exact @GlobalTheory.quotFam_represents | exact GlobalTheory.quotFam_represents | (intros; apply GlobalTheory.quotFam_represents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleGenericLocal

theorem exists_relAmple (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  obtain ⟨V, hV, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec A (IsLocalRing.closedPoint O : Sp O)) trivial
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine O A hA V hV fun s => ⟨eSec A s, ?_, ?_⟩
  · exact ((IsLocalRing.specializes_closedPoint (R := O) s).map (eSec A).continuous).mem_open V.isOpen hmem
  · rw [← Scheme.Hom.comp_apply, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]
    rfl

theorem exists_sec_fibre {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) (A' : Over (Sp K))
    (φ : A'.left ⟶ A.left) (hpb : IsPullback φ A'.hom A.hom (spMap (algebraMap O K))) (N : LB A.left)
    (hN : N.IsLB) (t : (N.pull φ).Sec) (ht : ∃ j, t.f j ≠ 0) (K' : Type) [Field K'] (y : Sp K' ⟶ Sp O) :
    ∃ (s : (N.pull (pullback.fst A.hom y)).Sec) (j : _), s.f j ≠ 0 := by
  haveI := hA.proper
  haveI := hA.smooth
  obtain ⟨F⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom (pull_isLB hN (𝟙 A.left))
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨v, hv0, hv⟩ := (GlobalTheory.GenericSection.exists_sec_iff F (algebraMap O K) hpb
    (Category.comp_id φ).symm).1 ⟨t, ht⟩
  let g' : O →+* K' := (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom g') = y := by simp [g']
  have H' : IsPullback (pullback.fst A.hom y) (pullback.snd A.hom y) A.hom
      (Spec.map (CommRingCat.ofHom g')) := by
    rw [hy]
    exact IsPullback.of_hasPullback A.hom y
  exact (GlobalTheory.GenericSection.exists_sec_iff F g' H' (Category.comp_id _).symm).2
    (GlobalTheory.GenericSection.exists_ker_ne_zero _ g' hinj _ v hv0 hv)

section Cube

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.EffectiveCube

theorem exists_sections_cube_cover {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀) (N : LB B.left)
    (s : N.Sec) (hN : N.IsLB) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  obtain ⟨j, hj⟩ := hs
  haveI := hB.comm
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hB hH hamp hN
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) B.hom).flip
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  let π : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  have hD : (((snd T B).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T B).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ B := Over.homMk (pointOfClosedPoint B.hom y hy) (pointOfClosedPoint_comp B.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply B.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp B.hom y hy)
  have good : ∀ a : T ⟶ B, (Out.ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 B).left) (fun _ => 1) y := fun a ha => by
    apply unitAt_pull s _ y
    have e : x ≫ ((π ≫ a) * 𝟙 B) = Out.ptSecT B (a * x) ≫ snd T B := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 B) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : B ⟶ B).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : B ⟶ B => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine' exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end Cube

theorem relAmple_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  intro O K _ _ _ _ _ _ _ _ A _ A' _ φ hA hpb M M' hM hM' e hamp
  obtain ⟨L, hL, hLa⟩ := exists_relAmple O A hA
  haveI := hA.proper
  haveI := hA.smooth
  have hpb' : IsPullback φ A'.hom A.hom (spMap (algebraMap O K)) := hpb.1
  haveI hA'p : IsProper A'.hom := MorphismProperty.of_isPullback hpb' hA.proper
  have hampφ : Out.RelAmple A' (M.pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr hM' (pull_isLB hM φ) e).1 ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' hM').1 hamp))
  have hne : Nonempty A'.left := ⟨eSec A' (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K A' (L.pull φ) (M.pull φ) hA'p hne
    (pull_isLB hL φ) (pull_isLB hM φ) hampφ
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div (LB.isLB_linComb hM _ _) hL
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (LB.div (lbPow (M.pull f) a) (L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB hL f)
  obtain ⟨t, ht⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN φ) (hN' φ)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM φ a) ⟨s, hs⟩
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨t', j, ht'⟩ := exists_sec_fibre A hA A' φ hpb' _ hN t ht K' y
  have hB : IsAbelianScheme ((Over.pullback y).obj A) := Out.TLinPf.isAb_pullback y A hA
  have hpbB : IsPullback (pullback.fst A.hom y) ((Over.pullback y).obj A).hom A.hom y :=
    IsPullback.of_hasPullback A.hom y
  have hLB : Out.RelAmple ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange hpbB hL (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hLa
  obtain ⟨t'', ht''⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst A.hom y) a).symm ⟨t', j, ht'⟩
  obtain ⟨r, u, hu⟩ := exists_sections_cube_cover ((Over.pullback y).obj A) hB (pull_isLB hL _) hLB _ t''
    (hN' _) ht''
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine _ (pull_isLB hM _)
    (GlobalTheory.relAmple_of_cube_div_generated K' ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y))
      (M.pull (pullback.fst A.hom y)) a r u hB.proper (pull_isLB hL _) (pull_isLB hM _) ha hLB hu)

end GlobalTheory.AmpleGenericLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_genericFibre_normalLocalDomain : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  first | exact @GlobalTheory.AmpleGenericLocal.relAmple_of_generic | exact GlobalTheory.AmpleGenericLocal.relAmple_of_generic | (intros; apply GlobalTheory.AmpleGenericLocal.relAmple_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj.PerUnit

theorem dataFrom_ofDeg {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (ω : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ))
    (n : ℕ) (D : DegPre V) (hB : D.TauBimult) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left)
    (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))
    (h : From T ω s ε n D e β β₂ w) : DataFrom T ω s ε n (GlobalTheory.PolDeg.Wit.ofDeg D hB) e := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun a b => ?_⟩
  obtain ⟨k, hk, hv⟩ := h₅ a b
  exact ⟨k, hk, fun z J J' hJ hJ' => ((GlobalTheory.PolDeg.Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ').trans (hv z J J' hJ hJ')⟩

theorem exists_good_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (z : (TK V).left) :
    ∃ J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L z J ∧
      ∀ e : Sp V ⟶ D.P.A.left, e (closedPoint V) ∈ D.P.L.U (J ((TK V).hom ≫ e)) := by
  classical
  haveI : IsDominant (jK V) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  have hinj : ∀ e e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = (TK V).hom ≫ e' → e = e' :=
    fun e e' h => ext_of_isDominant (jK V) h
  have hsp : ∀ (e : Sp V ⟶ D.P.A.left) (p : Sp V) (i : D.P.L.ι), e (closedPoint V) ∈ D.P.L.U i → e p ∈ D.P.L.U i :=
    fun e p i h => (((PrimeSpectrum.le_iff_specializes p (closedPoint V)).1
      (IsLocalRing.le_maximalIdeal p.2.ne_top)).map e.continuous).mem_open (D.P.L.U i).isOpen h
  choose pick hpick using exists_chart D.P.isLB
  refine ⟨fun ψ => if h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ then pick (h.choose (closedPoint V))
    else pick (ψ z), fun ψ => ?_, fun e => ?_⟩
  · by_cases h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ
    · simp only [dif_pos h]
      have e1 : ψ z = ((TK V).hom ≫ h.choose) z :=
        (congrArg (fun q : (TK V).left ⟶ D.P.A.left => q z) h.choose_spec).symm
      rw [e1]
      exact hsp _ _ _ (hpick _)
    · simp only [dif_neg h]
      exact hpick _
  · have h : ∃ e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e' = (TK V).hom ≫ e := ⟨e, rfl⟩
    simp only [dif_pos h]
    rw [hinj _ _ h.choose_spec]
    exact hpick _

theorem val_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {X Y : Scheme.{0}} {L : LB X} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp V ⟶ Y) (z : (TK V).left)
    (J : ((TK V).left ⟶ X) → L.ι) (hJ : ∀ k, (y ≫ φ k) (closedPoint V) ∈ L.U (J ((TK V).hom ≫ y ≫ φ k))) :
    ∃ w : Vˣ, val t ((TK V).hom ≫ y) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) w)) := by
  have hall : ∀ p : Sp V, y p ∈ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) := by
    intro p
    refine Set.mem_iInter.2 fun k => ?_
    have hsp : p ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint V)).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
    have hm := hJ k
    rw [← Category.assoc] at hm
    exact hsp.map (y ≫ φ k).continuous |>.mem_open (L.U _).isOpen hm
  have hU : y ⁻¹ᵁ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) = ⊤ := top_unique fun p _ => hall p
  have key : ∀ (U : (Sp V).Opens) (_ : U = ⊤) (a : Γ(Sp V, U)ˣ), ∃ w : Vˣ,
      gm (TK V).hom z U a = gm (TK V).hom z ⊤ (unitOn w) := by
    rintro U rfl a
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
    show a.val = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨w, hw⟩ := key _ hU (pullU y _ (t.s (fun k => J (((TK V).hom ≫ y) ≫ φ k))))
  refine ⟨w, ?_⟩
  have q : (toUnit (TK V)).left = (TK V).hom := by simp
  rw [← GlobalTheory.PolDeg.Taut.gm_jK_unitOn, q, ← hw]
  exact (gm_pull (TK V).hom y z _ (hall _) _).symm

end GlobalTheory.TInj.PerUnit

namespace GlobalTheory.TInj.PerUnit


set_option maxHeartbeats 2000000 in
theorem monomial_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  intro o W _ _ _ T I _ ε n V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hB₁ hB₂ f₁ f₂ m y y'
  obtain ⟨k₁, hk₁, U₁, -, hU₁⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₁ s₁ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₁ hB₁) e₁
    (dataFrom_ofDeg T ω₁ s₁ ε n D₁ hB₁ e₁ β₁ ββ₁ w₁ f₁) y (φ.symm.toAddMonoidHom (φ y'))
  obtain ⟨k₂, hk₂, U₂, -, hU₂⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₂ s₂ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₂ hB₂) e₂
    (dataFrom_ofDeg T ω₂ s₂ ε n D₂ hB₂ e₂ β₂ ββ₂ w₂ f₂) (φ y) (φ y')
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) hB₁ y
  obtain ⟨g', ha, hg'⟩ := m.2.2.2.2 y g hg
  obtain ⟨u, hu⟩ := m.2.2.2.1 (φ y')
  let z : (TK V).left := closedPoint (FractionRing V)
  obtain ⟨J₁, gJ₁, cJ₁⟩ := exists_good_closed D₁ z
  obtain ⟨J₂, gJ₂, cJ₂⟩ := exists_good_closed D₂ z
  obtain ⟨J, hJ, hl, hr⟩ := exists_good_join D₁.P.isLB D₂.P.isLB gJ₁ gJ₂
  have key := act_val_frac V D₂ D₁ b φ.symm.toAddMonoidHom F y (φ y) g g' hg hg' ha (φ y') u hu z J hJ
  have t₁ := ((GlobalTheory.PolDeg.Wit.exists_tau D₁ y (φ.symm.toAddMonoidHom (φ y'))).choose_spec.2 _ (𝟙 _) z (rl J)
    ((isPart_inl _ _).good hJ)).symm.trans (hU₁ z (rl J) ((isPart_inl _ _).good hJ))
  have t₂ := ((GlobalTheory.PolDeg.Wit.exists_tau D₂ (φ y) (φ y')).choose_spec.2 _ (𝟙 _) z (rr J)
    ((isPart_inr _ _).good hJ)).symm.trans (hU₂ z (rr J) ((isPart_inr _ _).good hJ))
  obtain ⟨v₁, hv₁⟩ := val_closed U₁ (𝟙 _) z (rl J) (fun k => by erw [hl]; exact cJ₁ _)
  obtain ⟨v₂, hv₂⟩ := val_closed U₂ (𝟙 _) z (rr J) (fun k => by erw [hr]; exact cJ₂ _)
  obtain ⟨v₃, hv₃⟩ := val_closed u (D₁.c y).left z J (fun k => by
    rcases k with k | k
    · have h1 := cJ₁ ((D₁.c y).left ≫ D₁.Oφ (𝟙 _) (φ.symm.toAddMonoidHom (φ y')) k)
      erw [← hl] at h1
      have h2 := ((isPart_inl D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inl, Category.assoc] at h2 ⊢
      exact h2
    · have h1 := cJ₂ ((D₁.c y).left ≫ D₂.Oφ b (φ y') k)
      erw [← hr] at h1
      have h2 := ((isPart_inr D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inr, Category.assoc] at h2 ⊢
      exact h2)
  have q₁ : (toUnit (TK V)).left = (TK V).hom ≫ 𝟙 (Sp V) := by simp
  have q₃ : ptK (D₁.c y) = (TK V).hom ≫ (D₁.c y).left := by simp [ptK]
  rw [← q₁] at hv₁ hv₂
  rw [← q₃] at hv₃
  have um : ∀ a c : (FractionRing V)ˣ, unitOn (a * c) = unitOn a * unitOn c := fun a c => map_mul _ a c
  have E : gm (𝟙 (TK V).left) z ⊤ (unitOn (k₂ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₂)) =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k₁ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₁ *
        Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₃)) := by
    rw [um, um, um, map_mul, map_mul, map_mul, ← hv₁, ← hv₂, ← hv₃, ← t₂, ← t₁]
    exact key
  have inj := GlobalTheory.DefectHom.gm_unitOn_inj z E
  have hc := congrArg (fun x : (FractionRing V)ˣ => (x : FractionRing V)) inj
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hc
  have hk₁' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
    have h' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ (φ.symm (φ y')))) := by
      exact hk₁
    rw [h', φ.symm_apply_apply]
  have hk₂' : (k₂ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) := by
    exact hk₂
  refine ⟨v₁ * v₃ * v₂⁻¹, ?_⟩
  rw [← hk₂', ← hk₁']
  have hv2 : algebraMap V (FractionRing V) (v₂ : V) * algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(k₂ : FractionRing V)) * hv2 + algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) * hc

end GlobalTheory.TInj.PerUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  first | exact @GlobalTheory.TInj.PerUnit.monomial_ratio_unit | exact GlobalTheory.TInj.PerUnit.monomial_ratio_unit | (intros; apply GlobalTheory.TInj.PerUnit.monomial_ratio_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmple

theorem exists_relAmple (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W))
    [GrpObj G] (hG : IsAbelianScheme G) : ∃ L : LB G.left, L.IsLB ∧ Out.RelAmple G L := by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec G (IsLocalRing.closedPoint W)) trivial
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine W G hG V hV fun s => ⟨eSec G s, ?_, ?_⟩
  · have hsp : (s : PrimeSpectrum W) ⤳ IsLocalRing.closedPoint W :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal s.2.ne_top)
    exact (hsp.map (eSec G).continuous).mem_open V.isOpen hx
  · rw [← Scheme.Hom.comp_apply, he]
    rfl

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem exists_generating_sq (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K']
    [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left)
    (hN : N.IsLB) (σ : (N.pull (pullback.fst G.hom (spMap (algebraMap W K')))).Sec) (hσ : ∃ j, σ.f j ≠ 0) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw N 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hK := IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))
  have hk := IsPullback.of_hasPullback G.hom (spMap (IsLocalRing.residue W))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hk
  obtain ⟨-, ⟨t, -, a, x, hx, hxa⟩, -⟩ := GlobalTheory.DvrModel.existsUnique_zpow_mul_sec hK hk hϖ hN σ hσ
  let F := AlgebraicClosure K'
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K' F).comp (algebraMap W K'))
  let g : W →+* O := ((algebraMap K' F).comp (algebraMap W K')).codRestrict O.toSubring hO
  have : IsLocalHom g := hloc
  have hg : Function.Injective g := fun a b e =>
    IsFractionRing.injective W K' ((algebraMap K' F).injective (congrArg Subtype.val e))
  have hflat : g.Flat := by
    letI := g.toAlgebra
    have : Module.IsTorsionFree W O := Module.isTorsionFree_iff_algebraMap_injective.2 hg
    exact (inferInstance : Module.Flat W O)
  have : Surjective (spMap g) := by
    letI := g.toAlgebra
    have : Module.Flat W O := hflat
    have : IsLocalHom (algebraMap W O) := ‹_›
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := O)
    exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩
  let B : Over (Sp O) := (Over.pullback (spMap g)).obj G
  let π : B.left ⟶ G.left := pullback.fst G.hom (spMap g)
  have h : IsGrpPullback B G (spMap g) π := isGrpPullback_pullback G _
  have hB : IsAbelianScheme B := by
    have hc : IsCommMonObj B := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  have := hB.comm
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  have hr : Out.Rigidified G N := DVR.exists_gen_of_isLB_local (V := W) _ (pull_isLB hN _)
  obtain ⟨R, hR, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.allSixLaws.1 _ G hG N hN hr
    (GlobalTheory.GenericAmpleDvr.triv_theta hG hN)
  subst hR
  obtain ⟨hLB, hr', ⟨c', -⟩, -⟩ := Out.CubePf.cubePull _ _ G B (cubeMapOf h) R c
  have cube : GlobalTheory.AbLaw.Triv (Theta B (R.L.pull π)) := ⟨c'.t, c'.isGen⟩
  obtain ⟨⟨t', ht', -⟩, H⟩ := GlobalTheory.SecPullIso.section_pull _ _ π _ _ _ hN (pull_isLB hN π)
    (Out.CubePf.idIsoL_isGen (pull_isLB hN π)) t
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap g) x
    (IsLocalRing.closedPoint O) (hx.trans (IsLocalRing.comap_closedPoint g).symm)
  have hmem : z ∈ Out.nonzeroLocus t' := by
    rw [H t' ht']
    exact (congrArg (· ∈ Out.nonzeroLocus t) hz₁).mpr (TopologicalSpace.Opens.mem_iSup.2 ⟨a, hxa⟩)
  have hu := GlobalTheory.SquareGenerated.exists_secs_sq_generate O F B hB _ (pull_isLB hN π) cube t' ⟨z, hmem, hz₂⟩
  rw [← GlobalTheory.AmpleCrit.pull_pw_eq] at hu
  obtain ⟨m, u, hu⟩ := hu
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  exact GlobalTheory.AmpleCrit.exists_cover_of_pull g hflat G.hom π B.hom h.1 (GlobalTheory.AbLaw.isLB_pw hN _) u hu

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem veryAmpleBy_pw_of_generic : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s → M.IsLB → w.IsGen → ∃ n : ℕ, 1 ≤ n ∧ ∃ (m' : ℕ) (t : Fin (m' + 1) → (GlobalTheory.AbLaw.pw M n).Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom (GlobalTheory.AbLaw.pw M n) t := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s M w hH hva hM hw
  have := hG.proper
  have := hA.proper
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have : IsProper (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))) ‹IsProper G.hom›
  have hHa : Out.RelAmple A H := GlobalTheory.MulFiniteAny.relAmple_of_veryAmpleBy' hH s hva
  have sq : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    have h1 : IsPullback e.hom.left (pullback.snd G.hom (spMap (algebraMap W K')))
        (pullback.snd A.hom (spMap (algebraMap K K'))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simpa using Over.w e.hom⟩
    simpa using h1.paste_horiz (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K')))
  have hHK := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hH hHa sq
  have hMK : Out.RelAmple (Over.mk (pullback.snd G.hom (spMap (algebraMap W K'))))
      (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) := by
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hH _)] at hHK
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)]
    exact (GlobalTheory.isAmpleLB_congr (pull_isLB hM _) (pull_isLB hH _) ⟨w, hw⟩).2 hHK
  obtain ⟨L, hL, hLa⟩ := exists_relAmple W G hG
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  have hne : Nonempty (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).left :=
    ⟨pullback.lift (spMap (algebraMap W K') ≫ eSec G) (𝟙 _) (by rw [Category.assoc, he]; simp)
      (IsLocalRing.closedPoint K')⟩
  obtain ⟨a, σ, ha, hσ⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K'
    (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))) (L.pull (pullback.fst G.hom (spMap (algebraMap W K'))))
    (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) inferInstance hne (pull_isLB hL _) (pull_isLB hM _) hMK
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div hp hL
  obtain ⟨σ', hσ'⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN _)
    (LB.isLB_div (LB.isLB_linComb (pull_isLB hM _) _ _) (pull_isLB hL _))
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst G.hom (spMap (algebraMap W K'))) a) ⟨σ, hσ⟩
  obtain ⟨r, u, hu⟩ := exists_generating_sq W K' G hG _ hN σ' hσ'
  have hiso : LBIso (lbPow (LB.div (lbPow M a) L) 2) (GlobalTheory.AbLaw.pw (LB.div (lbPow M a) L) 2) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow hN 2) (GlobalTheory.AbLaw.isLB_pw hN 2)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hN, GlobalTheory.AmpleStabFinite.cls_pw hN]
    first
      | rfl
      | exact (natCast_zsmul _ 2).symm
      | exact natCast_zsmul _ 2
      | simp only [two_smul, two_nsmul]
      | (simp; done)
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2)
    (GlobalTheory.AbLaw.isLB_pw hN _) hiso (u i)
  have hcov : ⨆ i, Out.nonzeroLocus (v i) = ⊤ := by
    simp_rw [hv]
    exact hu
  have hLamp := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hL).1 hLa
  have hMa := (GlobalTheory.isAmpleLB_pow_iff hM ha).1 (hLamp.of_pow_div_generated hp (by norm_num) v hcov)
  have hMrel := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hM).2 hMa
  obtain ⟨n, hn, m', t, -, ht⟩ := GlobalTheory.AbLaw.veryAmpleBy_of_relAmple hM hMrel (𝟙 G.left) (Category.id_comp _) hM
    (GlobalTheory.lbIso_pull_id hM).symm
  exact ⟨n, hn, m', t, ht⟩

end GlobalTheory.ModelAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianModeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmple_power_of_extension_genericFibre_abelianModel : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s → M.IsLB → w.IsGen → ∃ n : ℕ, 1 ≤ n ∧ ∃ (m' : ℕ) (t : Fin (m' + 1) → (GlobalTheory.AbLaw.pw M n).Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom (GlobalTheory.AbLaw.pw M n) t := by
  first | exact @GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic | exact GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic | (intros; apply GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lb_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  intro R _ _ _ H _ _ _ _ L hL
  obtain ⟨M, hM, hML⟩ := GlobalTheory.LBExtDVR.exists_lineBundle_extension_genericFibre R (FractionRing R)
    H.left ((Over.pullback (jK R)).obj H).left H.hom (pullback.snd H.hom (jK R))
    (pullback.fst H.hom (jK R)) inferInstance inferInstance (IsPullback.of_hasPullback H.hom (jK R)) L hL
  exact ⟨M, hM, LBIso.symm hML⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.lb_extends_over_dvr | exact GlobalTheory.Mum.lb_extends_over_dvr | (intros; apply GlobalTheory.Mum.lb_extends_over_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEqui
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEqui
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsPt_exists_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  intro R _ _ _ J hJ D A G _ _ U hG F _ _ _ k hk
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.exists_tors_closed R J hJ D A G hG U F k hk
  refine ⟨fun p => ⟨f p, (hf.1 p (f p)).2 rfl, ?_⟩, fun p p' x h h' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · exact (hf.2.2.1 p p').1 (((hf.1 p x).1 h).symm.trans ((hf.1 p' x).1 h'))

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  first | exact @GlobalTheory.TInj.torsPt_exists_inj | exact GlobalTheory.TInj.torsPt_exists_inj | (intros; apply GlobalTheory.TInj.torsPt_exists_inj <;> assumption)
end
end

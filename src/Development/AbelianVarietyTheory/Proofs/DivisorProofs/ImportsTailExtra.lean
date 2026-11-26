module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometries
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLineGen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffWeilIsAbelianPart
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.WeilAbelianPart

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem translPt_eq (b : TF (R := R) F ⟶ D.P.A) : translPt D.P.A b = DegPre.trPt D F b ≫ DegPre.prB D F :=
  (_root_.mul_comm (fst (TF (R := R) F) D.P.A ≫ b) (DegPre.prB D F)).trans (tr_pr D F b).symm

theorem translT_eq (b : TF (R := R) F ⟶ D.P.A) : translT D.P.A b = DegPre.trPt D F b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tr_fst, translT, lift_fst]
  · rw [translT, lift_snd, translPt_eq]

theorem exists_theta (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) (w : Frm D F k p.g.b)
    (hw : w.IsGen) : ∃ θ : ThetaGrp D.P.A D.P.L (k : ℤ) (TF (R := R) F), θ.pt = p.g.b ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → ∀ (ρ : DegPre.BF D F ⟶ DegPre.BF D F) z J, Good D.P.L z J →
        sval (t.s 0) ρ.left z J = sval (s.s 0) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
          (CommPairing.tval θ ρ.left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw 0
  obtain ⟨v, hvg, hvv⟩ := exists_gen D.P.isLB (K' := Fin 2)
    (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A p.g.b).left])
    (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      have a := ThetaPow.prod_fam_zero D F k (fun q => h ((DegPre.trPt D F p.g.b).left ≫ q))
      have c : ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
        rw [hy, add_zero]; exact ThetaPow.prod_fam_zero D F k h
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (prod_neg _ _ a)) ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast, Over.comp_left]) u hu
  refine ⟨⟨p.g.b, v, hvg⟩, rfl, fun s t H ρ z J hJ => ?_⟩
  have e := (phiRel_iff hG p w hw s t).1 H 0 0 (by rw [hy, add_zero]) _ ρ z J hJ
  rw [← hv u hu hc _ ρ z J hJ, ← hvv _ _ z J hJ] at e
  exact e

theorem eq_of_sval {k : ℕ} (s : Fam D F k) (hs : ¬ ∀ j, (s.s 0).f j = 0) {c c' : F}
    (h : ∀ y J, Good D.P.L y J → sval ((c • s).s 0) (𝟙 _) y J = sval ((c' • s).s 0) (𝟙 _) y J) : c = c' := by
  by_contra hne
  refine hs fun j => sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e : s = (c - c')⁻¹ • (c • s + (-1 : F) • c' • s) := by
    rw [neg_one_smul, ← sub_eq_add_neg, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
  have e₀ : c' • s + (-1 : F) • c' • s = 0 := by rw [neg_one_smul, add_neg_cancel]
  have e₁ := sval_add (c' • s) ((-1 : F) • c' • s) 0 (𝟙 _) y hJ
  rw [e₀, UUA.sval_zero_of (s := (0 : Fam D F k).s 0) (fun _ => rfl) _ y J (hJ.mem _ _)] at e₁
  rw [e, sval_smul _ _ _ _ y hJ, sval_add _ _ _ _ y hJ, h y J hJ, ← e₁, mul_zero,
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

attribute [local instance] TorusExt.gtGroup in
theorem qkAdd_swap (hB : D.TauBimult) {k : ℕ} (p p' : QkPt D F k) : QkAdd p' p (TorusExt.qkAdd hB p p') := by
  have : TorusExt.qkAdd hB p p' = TorusExt.qkAdd hB p' p := TorusExt.qk_ext (add_comm _ _) (add_comm p.g p'.g)
  rw [this]
  exact TorusExt.qkAdd_qkAdd hB p' p

theorem weilQkIs_iff_weilIs_abelianPart : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, p.y = 0 → p'.y = 0 → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs D.toPre.P.A D.toPre.P.L k p.g.b p'.g.b (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ) := by
  intro hL R _ _ _ I hI D F _ _ _ k hk p p' hy hy' ζ
  have hG := hL.1.globalFns
  have hB := D.tau_bimult
  obtain ⟨Φ, h₁, -, h₃, -, h₅, -⟩ := PhiProj.phi_projective hL R I hI D F k hk
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F k p.g).1
  obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic R D.toPre F k p'.g).1
  obtain ⟨v, hv, ev⟩ := h₅ p p' _ w w' hw hw' (TorusExt.qkAdd_qkAdd hB p p')
  obtain ⟨v', hv', ev'⟩ := h₅ p' p _ w' w hw' hw (qkAdd_swap hB p p')
  obtain ⟨c, -, hc⟩ := h₃ _ v' v hv' hv
  rw [ev, ev'] at hc
  have hc' : ∀ s, Φ p w (Φ p' w' s) = c • Φ p' w' (Φ p w s) := fun s => LinearMap.congr_fun hc s
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun s => ((h₁ p w hw).2 _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ p' w' s) := fun s => ((h₁ p' w' hw').2 _ _).2 rfl
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hk 0
  obtain ⟨t, rfl, -⟩ := FamFree.exists_fam_single hG hB hk 0 σ
  obtain ⟨t, rfl⟩ := (h₁ p' w' hw').1.2 t
  obtain ⟨s, rfl⟩ := (h₁ p w hw).1.2 t
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' c (fun s s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ => by
    rw [((h₁ p w hw).2 _ _).1 a₂, ((h₁ p' w' hw').2 _ _).1 a₁, ((h₁ p' w' hw').2 _ _).1 a₄,
      ((h₁ p w hw).2 _ _).1 a₃, hc']) ⟨s, _, _, r s, r' _, fun h0 => hσ fun j => by rw [h0]; rfl⟩ hk (ζ : F)
  obtain ⟨θ, hp, hθ⟩ := exists_theta hG p hy w hw
  obtain ⟨θ', hp', hθ'⟩ := exists_theta hG p' hy' w' hw'
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c₀ :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c₀, Units.ext (by simp [unitOn])⟩
  have hz := GlobalLift.weilIs_of_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB hc₀
  rw [hp, hp'] at hz
  have hcz : c = (z : F) := eq_of_sval _ hσ fun y J hJ => by
    have e := congrArg Units.val ((CommPairing.commIsOf_iff D.toPre.P.isLB θ θ' _).1 hc₀ _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial, hp, hp', translT_eq, translT_eq] at e
    have a₂ := hθ _ _ (r (Φ p' w' s)) (𝟙 _) y J hJ
    have a₁ := hθ' _ _ (r' s) (𝟙 _ ≫ DegPre.trPt D.toPre F p.g.b) y J hJ
    have a₄ := hθ' _ _ (r' (Φ p w s)) (𝟙 _) y J hJ
    have a₃ := hθ _ _ (r s) (𝟙 _ ≫ DegPre.trPt D.toPre F p'.g.b) y J hJ
    rw [a₁] at a₂
    rw [a₃] at a₄
    simp only [Category.id_comp, Over.id_left] at a₂ a₄ e
    rw [← hc', sval_smul _ _ _ _ y hJ, a₂, a₄, tr_comm, _root_.mul_assoc, _root_.mul_comm (Units.val _), e,
      Category.id_comp]
    show _ * (_ * _ * gs _ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (z : F))) = _
    ring
  rw [key, hcz]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective
      (CommutatorPairing.weilIs_unique hG D.toPre.P.isAb D.toPre.P.isLB H hz))

end GlobalTheory.UT.WeilAbelianPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomain
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem tateIso_spread : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  intro E _ _ _ H D R _ _ _ P act o _ s z k hk hrk pt F _ _ x₀ β₀ hd hx₀ I₀ hζ₀ hev₀ K _ _ _ x β hx
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have hu : ∀ {L : Type} [Field L] (y : Sp L ⟶ Sp R),
      (Over.homMk y (by simp) : Over.mk y ⟶ Out.baseOver (Sp R)) = toUnit (Over.mk y) := fun y =>
    Over.OverMorphism.ext ((Over.w (toUnit (Over.mk y))).symm.trans (Category.comp_id _))
  have hcard : ∀ n, 0 < n → Nat.card {w : Over.mk x ⟶ P.A // w ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [hrk]
    exact (hL.mulN _ P n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ P.A) (fun c w => w ≫ act c)
    (fun n w w' c => Out.WeilIs P.A P.L n w w' (unitOn c)) k (β z) _ (fun a : D.La => a)
    (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ pt a) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m w w' c hn hm hw hw' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact PELFamily.weilIs_lower P hL.weil hm u' hw hw' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp R) P act o s z _
        (fun a : D.La => a) pt (k * m) m hn (Dense.mono (fun p hp =>
          ⟨F, inferInstance, x₀, β₀, I₀.ζ (k * m), I₀.ev (k * m), Nat.cast_ne_zero.2 hn.ne', hp, hx₀,
            I₀.ζ_prim _ hn, I₀.add _, fun v => (I₀.onto _ hn _).2 ⟨v, rfl⟩, I₀.lin _, I₀.isom _ hn,
            by rw [← hζ₀, ← I₀.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I₀.tower k m hk hm _).trans ((hev₀ i).symm.trans (by rw [hu]))⟩) hd)
        K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.TorsIsometry.ker_and_onto E H D K (Over.mk x ⟶ P.A)
        (fun w w' c => Out.WeilIs P.A P.L (k * m : ℕ) w w' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => PELFamily.eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨I, hI, fun a => Eq.trans (by rw [hu]) (hA a).symm⟩

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoSpreadGenericNoetherianDomainStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_spread_generic_noetherian_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  first | exact @GlobalTheory.LowDat.tateIso_spread | exact GlobalTheory.LowDat.tateIso_spread | (intros; apply GlobalTheory.LowDat.tateIso_spread <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatum
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.GradedTate

theorem exists_tateIso_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H)
    (Z : Submodule (𝓞 E) Dw.La) (f : perp Dw Z →ₗ[𝓞 E] D'.La) (hf : IsLower Dw D' Z f) (K : Type) [Field K]
    (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (ζ : ℕ → Kˣ)
    (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (b : ℕ → perp Dw Z → Q) (hact : ∀ c, act c 1 = 1)
    (hcard : ∀ n, 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D'.La)
    (huniq : ∀ n x y c c', e n x y c → e n x y c' → c = c')
    (hone : ∀ n y c, e n 1 y c → c = 1)
    (hadd : ∀ n, 0 < n → ∀ a a', b n (a + a') = b n a * b n a')
    (hlin : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, b n (c • a) = act c (b n a))
    (hpow : ∀ n, 0 < n → ∀ a, b n a ^ n = 1)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, b (n * m) a ^ m = b n a)
    (hiso : ∀ n, 0 < n → ∀ a a', e n (b n a) (b n a') (ζ n ^ Dw.EF a a')) :
    ∃ I' : TateIso D' K Q act e, (∀ n, I'.ζ n = ζ n) ∧ ∀ n, 0 < n → ∀ a, b n a = I'.ev n (f a) := by
  have := D'.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf.1
  have hs' : ∀ w, f (s w) = w := fun w => LinearMap.congr_fun hs w
  have hiso' : ∀ n, 0 < n → ∀ a w', e n (b n a) (b n (s w')) (ζ n ^ D'.EF (f a) w') := fun n hn a w' => by
    have h := hiso n hn a (s w')
    rwa [← hf.2.2, hs'] at h
  have hiso'' : ∀ n, 0 < n → ∀ w w', e n (b n (s w)) (b n (s w')) (ζ n ^ D'.EF w w') := fun n hn w w' => by
    have h := hiso' n hn (s w) w'
    rwa [hs'] at h
  have hadd' : ∀ n, 0 < n → ∀ w w', b n (s (w + w')) = b n (s w) * b n (s w') := fun n hn w w' => by
    rw [map_add (f := _), hadd n hn]
  have hko := fun n (hn : 0 < n) => TorsIsometry.ker_and_onto E H D' K Q (e n) n (ζ n) (fun w => b n (s w)) hn
    (hcard n hn) (fun y c _ => hone n y c) (hζ n hn) (hadd' n hn) (fun w => hpow n hn _) (hiso'' n hn)
  refine ⟨{ ζ := ζ, ζ_prim := hζ, ζ_pow := hζ', ev := fun n w => if 0 < n then b n (s w) else 1
            add := fun n w w' => ?_, lin := fun n c w => ?_, ker := fun n hn => ?_, onto := fun n hn => ?_
            tower := fun n m hn hm w => ?_, isom := fun n hn w w' => ?_ }, fun _ => rfl, fun n hn a => ?_⟩
  · split_ifs with hn
    · exact hadd' n hn w w'
    · exact (_root_.mul_one _).symm
  · split_ifs with hn
    · rw [map_smul, hlin n hn]
    · exact (hact c).symm
  · simp only [if_pos hn]
    exact (hko n hn).1
  · simp only [if_pos hn]
    exact (hko n hn).2
  · simp only [if_pos hn, if_pos (Nat.mul_pos hn hm)]
    exact htow n m hn hm _
  · simp only [if_pos hn]
    exact hiso'' n hn w w'
  · show _ = if 0 < n then b n (s (f a)) else 1
    rw [if_pos hn]
    obtain ⟨w, hw⟩ := ((hko n hn).2 _).1 (hpow n hn a)
    obtain ⟨c, hc⟩ := TorsIsometry.exists_eq_nsmul_of_dvd D'.EF D'.unimod n (f a - w) fun w' => by
      have h₁ := hiso' n hn a w'
      rw [← hw] at h₁
      have h₂ := huniq _ _ _ _ _ h₁ (hiso'' n hn w w')
      rw [map_sub, LinearMap.sub_apply, ← (hζ n hn).zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    have h₃ : b n (s (f a - w)) = 1 := ((hko n hn).1 _).2 ⟨c, hc⟩
    have h₄ := hadd' n hn (f a - w) w
    rw [sub_add_cancel, h₃, _root_.one_mul] at h₄
    exact hw.symm.trans h₄.symm

section Pairs

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] TorusExt.gtGroup

theorem eq_of_equiv (hB : D.TauBimult) {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q)
    (hy : p.y = q.y) : p = q := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 h
  have hz : k • z = 0 := by
    rw [hy] at h₁
    exact left_eq_add.1 h₁
  have : z = 0 := by
    rw [← natCast_zsmul] at hz
    exact (smul_eq_zero.1 hz).resolve_left (Int.natCast_ne_zero.2 hk.ne')
  subst this
  rw [map_zero, add_zero] at h₂
  exact TorusExt.qk_ext hy h₂.symm

theorem b_pow (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) : p.g.b ^ k = 1 := by
  rw [← TorusExt.nsmul_b, TorusExt.qk_nsmul hB, hy, map_zero, TorusExt.zero_b]

theorem b_tower (hB : D.TauBimult) {n m : ℕ} (hn : 0 < n) {p p₀ : QkPt D F (n * m)} {q r r₀ : QkPt D F n}
    (hp : QkPt.Equiv D F p p₀) (hp₀ : p₀.y = 0) (hq : q.y = p.y) (hg : GtPtF.IsNsmul m p.g q.g)
    (hr : QkPt.Equiv D F q r) (hr' : QkPt.Equiv D F r r₀) (hr₀ : r₀.y = 0) : p₀.g.b ^ m = r₀.g.b := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 hp
  have h₃ : TorusExt.qkShift hB q (m • z) = r₀ := by
    refine eq_of_equiv hB hn (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB (TorusExt.equiv_qkShift hB q _))
      (TorusExt.equiv_trans hB hr hr')) ?_
    show q.y + n • m • z = r₀.y
    rw [hr₀, hq, smul_smul, ← h₁, hp₀]
  rw [← h₃, ← TorusExt.nsmul_b, h₂, nsmul_add, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hg, ← map_nsmul]
  rfl

end Pairs


attribute [local instance] TorusExt.gtGroup in
theorem exists_gradedTateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  intro E _ _ _ H Dw D' Z f hf R _ _ _ hR t P F _ _ _ hrk I hI
  letI := H.starRing
  have hB := P.D.tau_bimult
  have hL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have := hR.2
  have := hR.1.1
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  choose q hq hy using hI
  have huniq : ∀ (n : ℕ) (x y : TF (R := R) F ⟶ P.D.toPre.P.A) (c c' : Fˣ),
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c) →
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c') → c = c' := fun n x y c c' =>
    weilIs_unique_fieldPoint _ _ _ P.D.toPre.P.isLB F _ n x y c c'
  obtain ⟨I', h₁, h₂⟩ := exists_tateIso_of_perp Dw D' Z f hf F (TF (R := R) F ⟶ P.D.toPre.P.A)
    (fun a g => g ≫ P.oD.onB.act a)
    (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)) I.ζ I.ζ_prim I.ζ_pow
    (fun n a => if hn : 0 < n then (q n hn a).g.b else 1)
    (fun c => by
      have := P.oD.onB.hom c
      exact MonObj.one_comp _)
    (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      rw [hrk]
      exact (hL.1.mulN _ P.D.toPre.P n hn).2.2.2.2 F _
        (IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)).neZero'.ne)
    huniq
    (fun n y c h => by
      have h₁ := (hL.1.weil _ P.D.toPre.P n _).2.1 _ _ _ _ _ h h
      rw [_root_.mul_one] at h₁
      have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
      exact mul_eq_left.1 (huniq n 1 y _ _ (e ▸ h₁) h))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAdd_iff hB _ _ _).1
        ((TorusExt.qkAdd_iff_of_equiv hB (hq n hn a) (hq n hn a') (I.add n hn a a')).2 (hq n hn (a + a')))
      rw [← eq_of_equiv hB hn h (by
        show (q n hn a).y + (q n hn a').y = _
        rw [hy, hy, hy, add_zero])]
      exact TorusExt.add_b _ _)
    (fun n hn c a => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAct_iff hB hG P.oD _ _ _).1
        ((TorusExt.qkAct_iff_of_equiv hB hG P.oD (hq n hn a) (I.lin n hn c a)).2 (hq n hn (c • a)))
      rw [← eq_of_equiv hB hn h (by
        show c • (q n hn a).y = _
        rw [hy, hy, smul_zero])]
      exact TorusExt.gtSmul_b hG P.oD _ _)
    (fun n hn a => by
      simp only [dif_pos hn]
      exact b_pow hB _ (hy n hn a))
    (fun n m hn hm a => by
      simp only [dif_pos hn, dif_pos (Nat.mul_pos hn hm)]
      obtain ⟨r, r₁, r₂, r₃⟩ := I.tower n m hn hm a
      exact b_tower hB hn (hq _ _ a) (hy _ _ a) r₁ r₂ r₃ (hq n hn a) (hy n hn a))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      exact (UT.WeilAbelianPart.weilQkIs_iff_weilIs_abelianPart hL R _ hR.1 P.D F n hn _ _ (hy n hn a) (hy n hn a')
        _).1 (PhiOperatorCompare.weilQkIs_of_equiv hB (hq n hn a) (hq n hn a') (I.isom n hn a a')))
  refine ⟨I', h₁, fun n hn a r hr hr₀ => ?_⟩
  rw [← h₂ n hn a, dif_pos hn, eq_of_equiv hB hn
    (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB hr) (hq n hn a)) (hr₀.trans (hy n hn a).symm)]

end GlobalTheory.LowDat.GradedTate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatumStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gradedTateIso_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  first | exact @GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | exact GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | (intros; apply GlobalTheory.LowDat.GradedTate.exists_gradedTateIso <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometry
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.LowObj

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
  [IsLocalRing R] {I : Ideal R} {t : SAB H (Sp R)}

open GlobalTheory.CechPic in
theorem prim_of_gen {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (w : B ⟶ B) (L : LB B.left) (hL : L.IsLB)
    (r : LB.Gen (L.pull (eSec B))) (hr : r.IsGen)
    (u : LB.Gen (LB.LinComb L (K := Fin 4) ![(padd B (𝟙 _) w).left, 𝟙 B.left, w.left, (toUnit B ≫ η[B]).left]
      ![1, -2, -1, 2])) (hu : u.IsGen) : LBIso L (cubeLB B ![𝟙 _, w] L) := by
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_four] at h0
  have h1 : pull (eSec B) (cls _ hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨r, hr⟩
  have h2 : pull (toUnit B ≫ η[B]).left (cls _ hL) = 0 := by
    rw [Over.comp_left, pull_comp]
    exact (congrArg _ h1).trans (map_zero _)
  refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : B ⟶ B, padd B a b = a * b := fun _ _ => rfl
  simp only [pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h2, pull_id, smul_zero, add_zero,
    one_smul, neg_smul, Fin.isValue] at h0
  rw [lam, Hom.one_def, h2, Over.id_left, pull_id, add_zero, eq_comm, ← sub_eq_zero, ← h0]
  abel

theorem abPart_prim (P : PELUnif I t) :
    LBIso P.D.toPre.P.L (cubeLB P.D.toPre.P.A ![𝟙 _, (GlobalTheory.LocM.abPartAct P).act H.w0] P.D.toPre.P.L) := by
  letI := H.starRing
  obtain ⟨u, hu, -⟩ := P.w0
  exact prim_of_gen _ _ _ P.D.toPre.P.isLB P.D.toPre.rig P.D.toPre.rig_gen u hu

def abTriple (P : PELUnif I t) : SAB H (Sp R) where
  G := P.D.toPre.P.A
  semi := isSemiAbelian_of_isAbelianScheme _ P.D.toPre.P.isAb
  act := GlobalTheory.LocM.abPartAct P
  PP := ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩
  cub := P.D.toPre.cub
  sym := isSymmetric_of_symmetry_generator _ P.D.toPre.sym P.D.toPre.sym_gen P.D.toPre.sym_rig
  adj := fun a => by
    have h := GlobalTheory.LocM.abPartAct_isAdj E H R I t P a
    rwa [← GlobalTheory.LocM.bar_eq_star H] at h
  prim := abPart_prim P

end Triple

section Generic

variable (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem jFR_eq : jFK (R := R) F ≫ jK R =
    spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by
  rw [← Spec.map_comp]; rfl

theorem inj_jFR : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
  (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)

theorem dense_jFR : DenseRange (jFK (R := R) F ≫ jK R :) := by
  rw [jFR_eq]
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    exact ((RingHom.injective_iff_ker_eq_bot _).1 (inj_jFR R F)).le.trans bot_le)

variable {R F}

theorem section_ext {G : Over (Sp R)} [IsSeparated G.hom] {s s' : 𝟙_ (Over (Sp R)) ⟶ G}
    (h : toUnit (TF (R := R) F) ≫ s = toUnit (TF (R := R) F) ≫ s') : s = s' := by
  haveI : IsReduced (𝟙_ (Over (Sp R))).left := (inferInstance : IsReduced (Sp R))
  haveI : IsDominant (jFK (R := R) F ≫ jK R) := ⟨dense_jFR R F⟩
  have e : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm)
    (jFK (R := R) F ≫ jK R) ?_)
  rw [← e]
  exact congrArg (·.left) h

theorem exists_section [IsNoetherianRing R] [IsIntegrallyClosed R] [IsGalois (FractionRing R) F]
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : TF (R := R) F ⟶ G) (hx : x ^ n = 1)
    (hσ : ∀ σ : F ≃ₐ[FractionRing R] F, spMap (σ : F →+* F) ≫ x.left = x.left) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, toUnit _ ≫ s = x := by
  obtain ⟨y, hy⟩ := GlobalTheory.UnifDvrCompare.exists_point_of_fixed (F := FractionRing R) x.left hσ
  haveI : Epi (spMap (algebraMap (FractionRing R) F)) := by
    have h1 : Surjective (spMap (algebraMap (FractionRing R) F)) :=
      ⟨fun x => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  let y' : TK R ⟶ G := Over.homMk y (by
    rw [← cancel_epi (spMap (algebraMap (FractionRing R) F)), ← Category.assoc, hy]
    exact Over.w x)
  let u : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  haveI : Epi u := by
    haveI : Epi u.left := inferInstanceAs (Epi (spMap (algebraMap (FractionRing R) F)))
    exact Over.epi_of_epi_left _
  have hu : u ≫ y' = x := Over.OverMorphism.ext hy
  have hy' : y' ^ n = 1 := by
    rw [← cancel_epi u, MonObj.comp_pow, hu, hx, MonObj.comp_one]
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    show RingHom.ker (algebraMap R (FractionRing R)) ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _)]
    exact bot_le)⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.exists_section_of_pow_eq_one (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (jK R) G n (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (TK R) y' hy' (𝟙 _)
    (Category.id_comp _)
  refine ⟨Over.homMk s hs, Over.OverMorphism.ext ?_⟩
  have e : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (TF (R := R) F)))
  rw [Over.comp_left, e, ← hy]
  exact (Category.assoc _ _ _).trans (congrArg _ (hs'.trans (Category.id_comp _)))

theorem b_eq_of_equiv {D : DegPre R} {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q) (hp : p.y = 0)
    (hq : q.y = 0) : q.g.b = p.g.b := by
  obtain ⟨z, hz, g, hg, ha⟩ := h
  rw [hp, hq, zero_add, eq_comm, ← natCast_zsmul, smul_eq_zero_iff_right (Int.natCast_ne_zero.2 hk.ne')] at hz
  subst hz
  have c0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  rw [ha.1, hg.1, DegPre.cF, c0, MonObj.comp_one]
  exact _root_.mul_one p.g.b

end Generic

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem spMap_four {A B C D F : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing F] (a : A →+* B)
    (b : B →+* C) (c : C →+* D) (d : D →+* F) :
    spMap d ≫ spMap c ≫ spMap b ≫ spMap a = spMap ((d.comp (c.comp b)).comp a) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem rho_val (l : Level H) : ((baseKA l).ρ : ℂ) = H.rt0 := by simp [baseKA]

theorem rho_eq (l : Level H) (c : Coeff l) :
    (IntermediateField.inclusion (ka_le l c)) (baseKA (lowLevel l)).ρ = (IntermediateField.inclusion c.le) (baseKA l).ρ :=
  Subtype.ext (by simp only [IntermediateField.coe_inclusion, rho_val])

def lowF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : KA (lowLevel l) →+* F :=
  (toF C F).comp (IntermediateField.inclusion (ka_le l c)).toRingHom

theorem jFR_lowS (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (jFK (R := R) F ≫ jK R) ≫ lowS C = spMap (lowF C F) := by
  rw [Category.assoc]
  exact (congrArg (_ ≫ jK R ≫ ·) (spMap_comp _ _)).trans (spMap_four _ _ _ _)

theorem detCond_generic (hR : GlobalTheory.Mum.Base R) (C : UChart.Fam Xo c R) (D' : Datum H)
    (hp : D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X) (hq : D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] :
    DetCond D' (GlobalTheory.LocM.abPartAct C.P) (jFK (R := R) F ≫ jK R) (lowF C F (baseKA (lowLevel l)).ρ) := by
  haveI := hR.1.1
  haveI := hR.2
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% C.y_over]
    exact spMap_four _ _ _ _
  have hdet := (Xo.univ.geom F _ β hx).1
  have key : ∀ τ n, LieMult Xo.univ.t.act (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) τ n →
      LieMult (GlobalTheory.LocM.abPartAct C.P) (jFK (R := R) F ≫ jK R) τ (n - Module.finrank (𝓞 E) C.P.D.toPre.X) := by
    intro τ n h
    have h₁ := (lieMult_iff_of_isGrpPullback m2.cart tK.act Xo.univ.t.act m2.act (jFK (R := R) F) τ n).2 h
    have h₂ := (lieMult_iff_of_isGrpPullback m1.cart tK.act C.t.act m1.act (jFK (R := R) F) τ n).1 h₁
    rw [jFR_eq] at h₂ ⊢
    obtain ⟨m, hm, rfl⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P F _ (inj_jFR R F) τ n h₂
    rw [Nat.add_sub_cancel]
    exact hm
  intro τ
  have hρ : lowF C F (baseKA (lowLevel l)).ρ = β (baseKA l).ρ := congrArg (toF C F) (rho_eq l c)
  rw [hρ, hp, hq]
  exact ⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩

theorem finrank_eq_of_detCond (D : Datum H) {S : Scheme.{0}} (P : PolAV S) (act : OAct (𝓞 E) P.A) {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (ρ : k) (hρ : ρ ^ 2 = -(H.d : k)) (h : DetCond D act x ρ) :
    Module.finrank ℤ D.La = 2 * P.g := by
  classical
  have hd : (H.d : k) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hb : (IsCMField.ringOfIntegersComplexConj E) H.rt = -H.rt := by
    rw [← GlobalTheory.CharRank.bar_rt_neg H]
    exact RingOfIntegers.ext (by rw [H.bar_eq]; rfl)
  have hr := GlobalTheory.LieRankSum.rank_mul_finrank E S P.A P.g P.smoothDim act k x
    (fun τ => if τ H.rt = ρ then D.p else D.q) (D.p + D.q) (fun τ => by
      have hs : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ, map_neg, map_natCast]
      have h0 : ρ ≠ -ρ := fun e => hd (by
        have : ρ = 0 := by linear_combination (1 / 2 : k) * e
        rw [this] at hρ
        linear_combination hρ)
      have e : (τ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) H.rt = -τ H.rt := by
        rw [← map_neg, ← hb]; rfl
      rw [e]
      by_cases hτ : τ H.rt = ρ
      · refine ⟨by rw [if_pos hτ]; exact (h τ).1 hτ, ?_⟩
        rw [if_pos hτ, if_neg (by rw [hτ]; exact h0.symm)]
      · refine ⟨by rw [if_neg hτ]; exact (h τ).2 hτ, ?_⟩
        rw [if_neg hτ, if_pos (by rw [(sq_eq_sq_iff_eq_or_eq_neg.1 hs).resolve_left hτ, neg_neg]), add_comm])
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  rw [← hr, GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank, mul_comm]

theorem b_eq_of_level (hR : GlobalTheory.Mum.Base R) (C : UChart.Fam Xo c R)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    {F F' : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F']
    [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F')
    (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F))
    (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F'))
    (h : XFLevel C tK m1 m2 F I) (h' : XFLevel C tK m1 m2 F' I') (a : Dw.La)
    (q : QkPt C.P.D.toPre F l.M') (q' : QkPt C.P.D.toPre F' l.M')
    (e : QkPt.Equiv _ F (I.ev l.M' a) q) (e' : QkPt.Equiv _ F' (I'.ev l.M' a) q') (hq : q.y = 0) (hq' : q'.y = 0) :
    q'.g.b.left = spMap σ.toRingHom ≫ q.g.b.left := by
  haveI := hR.2
  have hM : 0 < l.M' := (lowLevel l).A_pos
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  obtain ⟨f, f₁, -, f₃, -⟩ := hT F l.M' hM
  obtain ⟨f', f₁', -, f₃', -⟩ := hT F' l.M' hM
  have hx := GlobalTheory.T.levelPoints_compat_of_tateIsometries Xo c R hR C tK m1 m2 F F' σ I I' h h' a _ _ ((f₁ _ _).2 rfl) ((f₁' _ _).2 rfl)
  rw [(f₃ _ _).2 e, (f₃' _ _).2 e'] at hx
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt C.P.D.tau_bimult σ.toRingHom (RingHom.ext σ.commutes) q
  have h₁ := (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R _ hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U F F' σ
    l.M' hM q r _ _ hr hx).1 ((f₁ _ _).2 rfl)
  rw [b_eq_of_equiv hM ((f₃' _ _).1 ((f₁' _ _).1 h₁).symm) (hr.1.trans hq) hq']
  exact hr.2.1

end Family

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_nsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) (n m : ℕ) (v : D.La) : I.ev n (m • v) = I.ev n v ^ m := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  | succ m ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem ev_eta {D : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {fm em : 𝓞 E} (hfm : fm ∈ l.Mb)
    (hfe : fm + em = 1) {m : ℕ} (hk : l.M' = l.M * m) {w : D.La}
    (hw : w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    I.ev l.M' (m • (em • w)) = I.ev l.M w := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by
    have := (lowLevel l).A_pos
    simp only [lowLevel] at this
    rw [hk, h, mul_zero] at this
    exact lt_irrefl 0 this
  rw [ev_nsmul, hk, I.tower _ _ hM hm]
  obtain ⟨c', hc'⟩ := GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D l l.prod hfm hw
  have h1 : w = em • w + l.M • c' := by rw [← hc', ← add_smul, add_comm, hfe, one_smul]
  conv_rhs => rw [h1]
  exact (GlobalTheory.CM.RationalTorsion.ev_add_smul I hM _ _).symm

theorem zeta_val (l : Level H) : ((baseKA l).ζ : ℂ) = zeta l.A := by simp [baseKA]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))


set_option maxHeartbeats 1000000 in
theorem exists_lowObj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C Z D' f hZ hlow hrk hp hq tK m1 m2 hI
  letI := H.starRing
  haveI := hR.1.1
  haveI := hR.2
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  let F0 := AlgebraicClosure (FractionRing R)
  haveI : CharZero F0 := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F0).injective
  obtain ⟨I0, hX0, hG0⟩ := hI F0
  rw [hrk] at hp hq
  have hdet0 := detCond_generic hR C D' hp hq tK m1 m2 F0
  have hρ0 : lowF C F0 (baseKA (lowLevel l)).ρ ^ 2 = -(H.d : F0) := by
    rw [← map_pow, (baseKA _).ρ_sq, map_neg, map_natCast]
  have hg := finrank_eq_of_detCond D' C.P.D.toPre.P (GlobalTheory.LocM.abPartAct C.P) _ _ hρ0 hdet0
  have hy : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F]
      (I : TateIsoQ Dw C.P.D.toPre C.P.oD F), FiltGraded C Z F I → ∀ n, 0 < n → ∀ a : perp Dw Z,
      ∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv _ F (I.ev n a) q ∧ q.y = 0 :=
    fun F _ _ I h n hn a => (h n hn a).2 ⟨a, a.2, 0, by simp⟩
  obtain ⟨J0, hJ0ζ, hJ0b⟩ := GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F0 hg I0 (hy F0 I0 hG0)
  have hM : 0 < l.M' := (lowLevel l).A_pos
  have hunit : IsUnit (l.M' : R) := by
    simpa using (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hM.ne') : IsUnit ((l.M' : ℕ) : c.F)).map C.b
  haveI := C.P.D.toPre.P.isAb.proper
  have hfix : ∀ (a : perp Dw Z) (σ : F0 ≃ₐ[FractionRing R] F0),
      spMap (σ : F0 →+* F0) ≫ (J0.ev l.M' (f a)).left = (J0.ev l.M' (f a)).left := by
    intro a σ
    obtain ⟨q, hq1, hq2⟩ := hy F0 I0 hG0 l.M' hM a
    rw [← hJ0b l.M' hM a q hq1 hq2]
    exact (b_eq_of_level hR C tK m1 m2 σ.toAlgHom I0 I0 hX0 hX0 a q q hq1 hq1 hq2 hq2).symm
  have hsec : ∀ w : D'.La, ∃ s : 𝟙_ (Over (Sp R)) ⟶ C.P.D.toPre.P.A, toUnit _ ≫ s = J0.ev l.M' w := by
    intro w
    obtain ⟨a, rfl⟩ := hlow.1 w
    exact exists_section C.P.D.toPre.P.A l.M' hunit _ ((J0.onto _ hM _).2 ⟨_, rfl⟩) (hfix a)
  choose sA hsA using hsec
  obtain ⟨fm, hfm, em, hem, hfe⟩ : ∃ x ∈ l.Mb, ∃ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), x + y = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  obtain ⟨m, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hζ0 : (J0.ζ l.M' : F0) = lowF C F0 (baseKA (lowLevel l)).ζ := by
    rw [hJ0ζ, hX0.1]
    exact congrArg (toF C F0) (Subtype.ext (by
      simp only [IntermediateField.coe_inclusion, zeta_val]; rfl))
  let o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C) :=
    { t := abTriple C.P
      proper := C.P.D.toPre.P.isAb.proper
      ample := C.P.D.toPre.P.ample
      ktriv := C.P.D.toPre.P.ktriv
      eta := fun w => sA (m • (em • w))
      eta_add := fun a b => section_ext (F := F0) (by
        erw [MonObj.comp_mul, hsA, hsA, hsA, smul_add, smul_add]; exact J0.add _ _ _)
      eta_ker := fun a ha => section_ext (F := F0) (by
        obtain ⟨c', hc'⟩ := GlobalTheory.CM.RationalTorsion.exists_eq_nsmul D' l (by rw [mul_comm]; exact l.prod) hem ha
        erw [MonObj.comp_one, hsA]
        exact (J0.ker _ hM _).2 ⟨c', by rw [hc', smul_smul, hk, mul_comm]⟩)
      etaA := sA
      etaA_add := fun a b => section_ext (F := F0) (by erw [MonObj.comp_mul, hsA, hsA, hsA]; exact J0.add _ _ _)
      etaA_ker := fun a => section_ext (F := F0) (by
        erw [MonObj.comp_one, hsA]
        exact (J0.ker _ hM _).2 ⟨a, rfl⟩)
      geom := by
        intro k _ _ x β hx
        haveI : CharZero k := charZero_of_injective_ringHom (f := β.comp (algebraMap ℚ (KA (lowLevel l))))
          (RingHom.injective _)
        refine ⟨GlobalTheory.DetSpread.detCond_of_dense E H D' (Sp R) C.P.D.toPre.P.A C.P.D.toPre.P.g
          (GlobalTheory.LocM.abPartAct C.P) (KA (lowLevel l)) (lowS C) (baseKA (lowLevel l)).ρ C.P.D.toPre.P.smoothDim
          (baseKA (lowLevel l)).ρ_sq ((dense_jFR R F0).mono ?_) k x β hx, ?_⟩
        · rintro _ ⟨p, rfl⟩
          exact ⟨F0, inferInstance, inferInstance, inferInstance, jFK (R := R) F0 ≫ jK R, lowF C F0, ⟨p, rfl⟩,
            jFR_lowS C F0, hdet0⟩
        obtain ⟨I, hIζ, hIev⟩ := GlobalTheory.T.tateIso_spread_generic_noetherian_domain D' R C.P.D.toPre.P (fun a => C.P.oD.onB.act a) (KA (lowLevel l)) (lowS C)
          (baseKA (lowLevel l)).ζ l.M' hM hg sA F0 (jFK (R := R) F0 ≫ jK R) (lowF C F0) (dense_jFR R F0)
          (jFR_lowS C F0) J0 hζ0 hsA k x β hx
        refine ⟨I, hIζ, hIev, fun w hw => ?_⟩
        exact (hIev _).trans (ev_eta l I hfm hfe hk hw) }
  refine ⟨o', 𝟙 _, GlobalTheory.SiegLower.isGrpPullback_id _, fun x => (Category.comp_id _).trans (Category.id_comp _).symm,
    GlobalTheory.SiegLower.lbIso_pull_id C.P.D.toPre.P.isLB, ?_⟩
  intro F _ _ _ I hX hG
  obtain ⟨J, hJζ, hJb⟩ := GlobalTheory.T.exists_gradedTateIso_lowerDatum Dw D' Z f hlow R hR C.t C.P F hg I (hy F I hG)
  have key : ∀ w, toUnit _ ≫ sA w = J.ev l.M' w := by
    intro w
    obtain ⟨a, rfl⟩ := hlow.1 w
    obtain ⟨σ⟩ : Nonempty (F0 →ₐ[FractionRing R] F) := ⟨IsAlgClosed.lift⟩
    obtain ⟨q, hq1, hq2⟩ := hy F I hG l.M' hM a
    obtain ⟨q0, h01, h02⟩ := hy F0 I0 hG0 l.M' hM a
    have e1 := b_eq_of_level hR C tK m1 m2 σ I0 I hX0 hX a q0 q h01 hq1 h02 hq2
    rw [hJb l.M' hM a q hq1 hq2, hJ0b l.M' hM a q0 h01 h02] at e1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, e1, ← hsA (f a), Over.comp_left, ← Category.assoc, toUnit_left, toUnit_left]
    have e : spMap σ.toRingHom ≫ jFK (R := R) F0 = jFK (R := R) F := by
      rw [← Spec.map_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (RingHom.ext fun r => σ.commutes r)
    show (jFK (R := R) F ≫ jK R) ≫ _ = (spMap σ.toRingHom ≫ jFK (R := R) F0 ≫ jK R) ≫ _
    rw [← Category.assoc (spMap _), e]
  refine ⟨J, fun n => hJζ n, key, fun w hw => ?_, fun n hn a => ?_⟩
  · show toUnit _ ≫ sA (m • (em • w)) = _
    rw [key]
    exact ev_eta l J hfm hfe hk hw
  · obtain ⟨q, hq1, hq2⟩ := hy F I hG n hn a
    exact ⟨q, hq1, hq2, by rw [hJb n hn a q hq1 hq2]; exact (Category.comp_id _).symm⟩

end Main

end GlobalTheory.LowDat.LowObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometryStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  first | exact @GlobalTheory.LowDat.LowObj.exists_lowObj | exact GlobalTheory.LowDat.LowObj.exists_lowObj | (intros; apply GlobalTheory.LowDat.LowObj.exists_lowObj <;> assumption)
end
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LowDat.exists_lower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
  GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R, 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    GlobalTheory.LowDat.IsLower Dw D' Z f ∧ D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : GlobalTheory.LowDat.LowTate C D' o' F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I ∧
          GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨Z, hZ, hrk, tK, m1, m2, hI⟩ := GlobalTheory.T.exists_isotropic_saturated_weight_filtration Xo c R hR C hr
  obtain ⟨D', f, hf, hp, hq⟩ := GlobalTheory.T.exists_lower_datum_of_isotropic_saturated Dw Z hZ
  obtain ⟨o', φB, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry Xo c R hR C Z D' f hZ hf hrk hp hq tK m1 m2 hI
  refine ⟨Z, D', f, o', φB, hZ, hrk, hf, hrk ▸ hp, hrk ▸ hq, h1, h2, h3, tK, m1, m2, ?_⟩
  intro F _ _ _
  obtain ⟨I, hI1, hI2⟩ := hI F
  obtain ⟨I', hI'⟩ := h4 F I hI1 hI2
  exact ⟨I, I', hI1, hI2, hI'⟩

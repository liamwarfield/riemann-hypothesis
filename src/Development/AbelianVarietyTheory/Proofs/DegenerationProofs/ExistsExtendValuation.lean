module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesAlgebraicClosureCompatible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldPowerSeriesExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldPowerSeriesExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_powerSeries :
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  intro O' _ _ K _ _ _ _
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, hle, hlt⟩ :=
    exists_complete_isAlgClosed_cExt (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))
  let ψ : PowerSeries (FractionRing O') →+* C :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).comp
      (algebraMap (PowerSeries (FractionRing O')) _)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).injective.comp
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O'))))
  let φ : PowerSeries O' →+* C := ψ.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hφ : Function.Injective φ :=
    hψ.comp (PowerSeries.map_injective _ (IsFractionRing.injective O' (FractionRing O')))
  let _ : Algebra (PowerSeries O') C := φ.toAlgebra
  have : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  let g : K →ₐ[PowerSeries O'] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap (PowerSeries O') K r) = φ r := fun r => g.commutes r
  have hX : φ PowerSeries.X ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hφ (h.trans (map_zero φ).symm))
  refine ⟨C, i1, i2, i3, i4, (ψ.comp PowerSeries.C).toAlgebra, g.toRingHom, Units.mk0 _ hX,
    fun x => ?_, fun r => ?_, (hg _).symm, ?_⟩
  · rw [hg]
    change ψ (PowerSeries.C _) = ψ (PowerSeries.map _ _)
    rw [PowerSeries.map_C]
  · rw [hg]
    exact hle _
  · change ‖ψ (PowerSeries.map _ PowerSeries.X)‖ < 1
    rw [PowerSeries.map_X]
    refine hlt _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldPowerSeriesExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension : ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries | exact GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_powerSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullAll
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMove
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMove
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullMove

theorem isThetaPt_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) :
    IsThetaPt P' k (fun i => x i ≫ φ.hom) v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have Q' := GlobalTheory.ThetaPtUp.isThetaPtOver_up (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q
  rw [IsIso.inv_id] at Q'
  exact Q'

def tateMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (F : Q ≃* Q')
    (ha : ∀ c x, F (act c x) = act' c (F x))
    (he : ∀ n x y c, x ^ n = 1 → y ^ n = 1 → e n x y c → e' n (F x) (F y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := F (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, ha]
  ker n hn a := by rw [F.map_eq_one_iff, I.ker n hn]
  onto n hn x := by
    obtain ⟨y, rfl⟩ := F.surjective x
    rw [← map_pow, F.map_eq_one_iff, I.onto n hn]
    exact exists_congr fun a => F.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he n _ _ _ ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b)

def ptEquiv {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A ≅ A') [IsMonHom φ.hom] (T : Over S) :
    (T ⟶ A) ≃* (T ⟶ A') where
  toFun x := x ≫ φ.hom
  invFun y := y ≫ φ.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := map_mul (IsMonHom.monoidHom φ.hom T)

theorem exists_tateIso_move : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  intro hL E _ _ _ H D K _ _ o o' φ ⟨hφ, t⟩ hact
  letI := H.starRing
  obtain ⟨w, hw⟩ := LBIso.symm t
  refine ⟨tateMap o.I (ptEquiv φ _) (fun c x => ?_) (fun n x y c hx hy h => ?_), rfl, fun _ _ => rfl, fun m v h => ?_⟩
  · show (x ≫ o.oa.act c) ≫ φ.hom = (x ≫ φ.hom) ≫ o'.oa.act c
    rw [Category.assoc, hact, Category.assoc]
  · exact (weilIs_iso_iff hL.globalFns hL.cube o.P o'.P φ w hw n x y hx hy _).2 h
  · exact isThetaPt_iso φ ⟨w, hw⟩ (fun a => (o.I.onto _ (pow_pos h.1.pos 2) _).2 ⟨a, rfl⟩) h

end GlobalTheory.FullMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMoveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_of_isPolIso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  first | exact @GlobalTheory.FullMove.exists_tateIso_move | exact GlobalTheory.FullMove.exists_tateIso_move | (intros; apply GlobalTheory.FullMove.exists_tateIso_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelOfFull
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelOfFull
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullLevel

section Abstract

variable {G L : Type} [CommGroup G] [AddCommGroup L] {r n : ℕ} {ev : L → G}

theorem ev_basis (add : ∀ a b, ev (a + b) = ev a * ev b) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) (c : Fin r → ℤ) :
    ev (bas c) = ∏ i, ev (bas (Pi.single i 1)) ^ c i := by
  let f : L →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ev a)) fun a b => by rw [add, ofMul_mul]
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin r → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : f (bas c) = ∑ i, c i • f (bas (Pi.single i 1)) := by
    conv_lhs => rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  have h' := congrArg Additive.toMul h
  rw [toMul_sum] at h'
  simp only [toMul_zsmul] at h'
  exact h'

theorem card_torsion (hn : 0 < n) (add : ∀ a b, ev (a + b) = ev a * ev b) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (onto : ∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) :
    Nat.card {x : G // x ^ n = 1} = n ^ r := by
  let f : (Fin r → Fin n) → {x : G // x ^ n = 1} := fun c => ⟨ev (bas fun i => (c i : ℕ)), (onto _).2 ⟨_, rfl⟩⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hb : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun x => ?_⟩
    · have h₁ : ev (bas fun i => (c i : ℕ)) = ev (bas fun i => (c' i : ℕ)) := congrArg Subtype.val h
      have h₂ := add (bas (fun i => (c i : ℕ)) - bas fun i => (c' i : ℕ)) (bas fun i => (c' i : ℕ))
      rw [sub_add_cancel, h₁] at h₂
      obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 h₂.symm)
      obtain ⟨b, rfl⟩ := bas.surjective b
      rw [← map_sub, ← map_nsmul] at hb
      funext i
      have h₃ : ((c i : ℕ) : ℤ) - (c' i : ℕ) = n * b i := by simpa using congrFun (bas.injective hb) i
      have h₄ : ((c' i : ℕ) : ℤ) ≡ (c i : ℕ) [ZMOD n] := (Int.modEq_iff_dvd).2 ⟨_, h₃⟩
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 h₄) (c' i).2 (c i).2).symm
    · obtain ⟨a, ha⟩ := (onto _).1 x.2
      obtain ⟨a, rfl⟩ := bas.surjective a
      have h₀ : ∀ i, 0 ≤ a i % n := fun i => Int.emod_nonneg _ hn'.ne'
      refine ⟨fun i => ⟨(a i % n).toNat, by have := Int.emod_lt_of_pos (a i) hn'; have := h₀ i; omega⟩,
        Subtype.ext ?_⟩
      have e : a = (fun i => (((a i % n).toNat : ℕ) : ℤ)) + n • fun i => a i / n := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.toNat_of_nonneg (h₀ i)]
        exact (Int.emod_add_mul_ediv _ _).symm
      rw [← ha]
      conv_rhs => rw [e, map_add (f := _), add, map_nsmul, (ker _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_eq_of_bijective f hb]
  simp

end Abstract

end GlobalTheory.FullLevel

namespace GlobalTheory


open FullLevel in
theorem exists_level_of_full : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  intro hL E _ _ _ H D g bas hb K _ _ o M hM
  have := o.charZero
  have := o.P.isAb.comm
  have : NeZero M := ⟨hM.ne'⟩
  have hg : o.P.g = g := by
    have h₁ := (hL.mulN _ o.P 2 one_le_two).2.2.2.2 K (𝟙 _) (by norm_num)
    have h₂ := card_torsion (G := baseOver (Sp K) ⟶ o.P.A) two_pos (o.I.add 2) (o.I.ker 2 two_pos)
      (o.I.onto 2 two_pos) bas
    have h₃ := Nat.pow_right_injective le_rfl (h₁.symm.trans h₂)
    omega
  subst hg
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : K →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom (o.I.ζ M)) M := fun φ =>
    (o.I.ζ_prim M hM).map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have tor : ∀ a, o.I.ev M a ^ M = 1 := fun a => (o.I.onto M hM _).2 ⟨a, rfl⟩
  obtain ⟨lev, hlev⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) o.P M (unitOn (o.I.ζ M))
    (by have := nt K; exact prim (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 hM.ne')
    (fun i => o.I.ev M (bas (Pi.single i 1))) (fun i => tor _)
    (fun i j => by
      have h := o.I.isom M hM (bas (Pi.single i 1)) (bas (Pi.single j 1))
      rw [hb] at h
      have e : unitOn (o.I.ζ M ^ stdSymp o.P.g i j) = unitOn (o.I.ζ M) ^ stdSymp o.P.g i j := map_zpow _ _ _
      exact e ▸ h)
  refine ⟨rfl, lev, fun i => congrFun hlev i, fun c => ?_⟩
  rw [levelPoint_rfl, Level.toPt, hlev, ev_basis (G := baseOver (Sp K) ⟶ o.P.A) (o.I.add M) bas c, linComb,
    List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (tor _)]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelOfFullStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_of_full' : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  first | exact @GlobalTheory.exists_level_of_full | exact GlobalTheory.exists_level_of_full | (intros; apply GlobalTheory.exists_level_of_full <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem isThetaPt_comp {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) : IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) (M r : ℕ) (a : D.La) : I.ev M (r • a) = I.ev M a ^ r := by
  induction r with
  | zero =>
    have := I.add M 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem theta_down (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] (o : Full D K) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {v v' : D.La → K} (c : Kˣ) (hc : ∀ x, v (r • x) = c * v' x) (h : o.Theta (r * m) v) : o.Theta m v' := by
  have e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a := fun a => by
    rw [ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]
    congr 2; ring
  have h₁ := GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul hL K o.P r m D.La _ _ (fun a => by
    rw [e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)
  have h₂ := isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁
  simp only [e] at h₂
  unfold Full.Theta
  convert h₂ using 2 with a
  rw [hc]
  exact (congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)

theorem exists_iso (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) (D : Datum H) {n : ℕ}
    (hn : n.Prime) (ho : Odd n) : ∃ J₀, ∀ J, J₀ ≤ J → ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (v : D.La → K),
      o.I.ζ ((n ^ J) ^ 2) = o'.I.ζ ((n ^ J) ^ 2) → o.Theta (n ^ J) v → o'.Theta (n ^ J) v →
      ∃ φ : o.P.A ≅ o'.P.A, IsPolIso o.P o'.P φ ∧
        (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) := by
  letI := H.starRing
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  generalize Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas
  choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  let B := ((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)
  refine ⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : B < n ^ (j + 4) := lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hp : 0 < n ^ (j + 4) := pow_pos hn.pos _
  set M := (n ^ (j + 4)) ^ 2 with hM
  have hM0 : 0 < M := pow_pos hp _
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI := o.charZero
  obtain ⟨hg, lev, hb, hl⟩ := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o M hM0
  have Q := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o' M hM0
  rw [← hζ] at Q
  obtain ⟨hg', lev', hb', hl'⟩ := Q
  let lab : (Fin (2 * g) → ZMod M) → D.La := fun a => bas fun i => ((a i).val : ℤ)
  have hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a := fun a => funext fun i => by simp
  have e : levelPoint lev hg = fun a => o.I.ev M (lab a) := funext fun a => by rw [← hl, hlab]
  have e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a) := funext fun a => by rw [← hl', hlab]
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ B := le_add_left (by gcongr)
      _ < n ^ (j + 4) := hB
      _ ≤ M := Nat.le_self_pow two_ne_zero _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨φ, hφ, hφb⟩ := h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K
    (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a)))
    (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)
  haveI := hφ.1
  have hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a := fun a => by
    obtain ⟨c, rfl⟩ := bas.surjective a
    rw [← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (linComb · _) (funext hφb)
  refine ⟨φ, hφ, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E)) := hs ▸ Submodule.mem_top
  have add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b := o.oa.map_add
  have add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b := o'.oa.map_add
  let f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom))
    fun a b => by rw [add, MonObj.mul_comp]; rfl
  let f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a))
    fun a b => by rw [add', MonObj.comp_mul]; rfl
  have : f = f' := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by
    refine congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg'
      φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)
    obtain ⟨b, rfl⟩ := (o.I.onto M hM0 y).1 hy
    have l := o.I.lin M a b
    have l' := o'.I.lin M a b
    rw [← Category.assoc, ← Category.assoc, ← l, hev, hev, l']
  exact Additive.ofMul.injective (DFunLike.congr_fun this x)

private theorem exists_finite_reps_local (L : Type) [AddCommGroup L] [Module.Finite ℤ L] {M : ℕ} (hM : 0 < M) :
    ∃ (A : Type) (_ : Finite A) (r : A → L), ∀ a, ∃ x b, a = r x + M • b := by
  let N : Submodule ℤ L := LinearMap.range ((M : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))
  have hfin : Finite (L ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(M : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hM.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    change (M : ℤ) • N.mkQ y = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨L ⧸ N, hfin, Quotient.out, fun a => ⟨Submodule.Quotient.mk a, ?_⟩⟩
  have h : a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) ∈ N :=
    (Submodule.Quotient.eq N).1 (Quotient.out_eq (Submodule.Quotient.mk a : L ⧸ N)).symm
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  have : M • b = a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) := by
    rw [← hb]; simp
  rw [this]; abel

private theorem ev_add_nsmul_local {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {M : ℕ} (hM : 0 < M) (a b : D.La) :
    I.ev M (a + M • b) = I.ev M a := by
  rw [I.add, (I.ker M hM _).2 ⟨b, rfl⟩, _root_.mul_one]

private theorem finite_level_local {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} {M : ℕ} (hM : 0 < M) :
    (Set.range fun I : TateIso D k Q act e => (I.ev M, I.ζ M)).Finite := by
  rcases isEmpty_or_nonempty (TateIso D k Q act e) with h | ⟨⟨I₀⟩⟩
  · exact Set.finite_range _
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨A, hA, r, hr⟩ := exists_finite_reps_local D.La hM
  have hT : {x : Q | x ^ M = 1}.Finite := by
    refine (Set.finite_range fun x => I₀.ev M (r x)).subset fun x hx => ?_
    obtain ⟨a, rfl⟩ := (I₀.onto M hM x).1 hx
    obtain ⟨y, b, rfl⟩ := hr a
    exact ⟨y, (ev_add_nsmul_local I₀ hM _ _).symm⟩
  have h₁ : (Set.range fun I : TateIso D k Q act e => I.ev M).Finite := by
    refine Set.Finite.of_finite_image (f := fun f => f ∘ r) ?_ ?_
    · refine (Set.Finite.pi' fun _ : A => hT).subset ?_
      rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩ x
      exact (I.onto M hM _).2 ⟨_, rfl⟩
    · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩ h
      funext a
      obtain ⟨y, b, rfl⟩ := hr a
      simp only [ev_add_nsmul_local _ hM]
      exact congrFun h y
  have h₂ : (Set.range fun I : TateIso D k Q act e => I.ζ M).Finite := by
    haveI : NeZero M := ⟨hM.ne'⟩
    have hfin : Finite (rootsOfUnity M k) := inferInstance
    refine Set.Finite.subset (s := (rootsOfUnity M k : Set kˣ)) hfin ?_
    rintro _ ⟨I, rfl⟩
    exact (I.ζ_prim M hM).pow_eq_one
  refine (h₁.prod h₂).subset ?_
  rintro _ ⟨I, rfl⟩
  exact ⟨⟨I, rfl⟩, ⟨I, rfl⟩⟩

private theorem exists_limit_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : ℕ → TateIso D k Q act e), ∃ I' : TateIso D k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  intro E _ _ _ H D k _ Q _ act e I
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have key : ∀ M, ∃ p : (D.La → Q) × kˣ, (∃ j, p.1 = (I j).ev M) ∧
      (0 < M → ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M) := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact ⟨((I 0).ev 0, 1), ⟨0, rfl⟩, fun h => absurd h (lt_irrefl _)⟩
    obtain ⟨p, -, hp⟩ := Ultrafilter.eq_pure_of_finite_mem (f := U.map fun j => ((I j).ev M, (I j).ζ M))
      (finite_level_local (D := D) (act := act) (e := e) hM)
      (Ultrafilter.mem_map.2 (Filter.univ_mem' fun j => ⟨I j, rfl⟩))
    have h : ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M := by
      have : {p} ∈ U.map fun j => ((I j).ev M, (I j).ζ M) := by rw [hp]; exact Ultrafilter.mem_pure.2 rfl
      filter_upwards [Ultrafilter.mem_coe.2 (Ultrafilter.mem_map.1 this)] with j hj
      have hj' : ((I j).ev M, (I j).ζ M) = p := hj
      rw [← hj']; exact ⟨rfl, rfl⟩
    exact ⟨p, h.exists.imp fun _ h => h.1, fun _ => h⟩
  choose p hp₀ hp using key
  have one : ∀ n, 0 < n → ∃ j, (p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n := fun n hn => (hp n hn).exists
  have two : ∀ n m, 0 < n → 0 < m → ∃ j, ((p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n) ∧
      (p (n * m)).1 = (I j).ev (n * m) ∧ (p (n * m)).2 = (I j).ζ (n * m) := fun n m hn hm =>
    ((hp n hn).and (hp _ (Nat.mul_pos hn hm))).exists
  refine ⟨{ ζ := fun n => (p n).2
            ev := fun n => (p n).1
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => ?_
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun M hM j₀ => ?_⟩
  · obtain ⟨j, -, h⟩ := one n hn
    rw [h]; exact (I j).ζ_prim n hn
  · obtain ⟨j, ⟨-, h⟩, -, h'⟩ := two n m hn hm
    rw [h, h']; exact (I j).ζ_pow n m hn hm
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).add n a b
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).lin n c a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).ker n hn a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).onto n hn x
  · obtain ⟨j, ⟨h, -⟩, h', -⟩ := two n m hn hm
    rw [h, h']; exact (I j).tower n m hn hm a
  · obtain ⟨j, h, h'⟩ := one n hn
    rw [h, h']; exact (I j).isom n hn a b
  · have h : ∀ᶠ j in (U : Filter ℕ), j₀ ≤ j := Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop j₀)
    exact (h.and (hp M hM)).exists

theorem exists_full_all (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) {K : Type} [Field K]
    [IsAlgClosed K] (ρ : K) (ζ : ℕ → Kˣ) (hζ : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (v : ℕ → D.La → K)
    (hv : ∀ r m, Odd r → Odd m → ∃ c : Kˣ, ∀ x, v (r * m) (r • x) = c * v m x) {n : ℕ} (hn : n.Prime) (ho : Odd n)
    (h : ∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = ρ ∧ o.I.ζ ((n ^ j) ^ 2) = ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (v (n ^ j))) :
    ∃ o : Full D K, o.ρ = ρ ∧ ∀ j, o.I.ζ (n ^ j) = ζ (n ^ j) ∧ o.Theta (n ^ j) (v (n ^ j)) := by
  obtain ⟨J, hJ⟩ := exists_iso hL h₁ h₂ D hn ho
  choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)
  have hp : ∀ i, 0 < n ^ i := fun i => pow_pos hn.pos i
  have th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i)) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨c, hc⟩ := hv (n ^ d) (n ^ i) ho.pow ho.pow
    refine theta_down hL (o j) (hp d) (hp i) c hc ?_
    rw [← pow_add, ← hd]; exact ht j
  have ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have := hz j
    rw [← pow_mul, mul_comm, hd, pow_add] at this
    rw [← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]
  have ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2) := fun j i hi => by
    rw [← pow_mul]; exact ze j _ (by omega)
  choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _
    ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)
  choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)
  obtain ⟨I', hI'⟩ := exists_limit_local E H D K _ _ _ I
  refine ⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, -, e⟩ := hI' _ (hp i) i
    exact e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))
  · obtain ⟨j, hj, e, -⟩ := hI' _ (pow_pos (hp i) 2) i
    have := hI j _ _ (th j i (by omega))
    unfold Full.Theta at this ⊢
    dsimp only at this ⊢
    rw [e]; exact this

end GlobalTheory.Ex.AllLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxNest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxNest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex.TwNest
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def Mult (t : N.X → Oˣ) (g : N.Gt) (g' : (N.twist β u).Gt) : Prop :=
  g'.b = g.b ∧ ∀ z : N.X, g'.s z = g.s z * t z

variable {β u}

theorem Mult.mul {t t' : N.X → Oˣ} {g h : N.Gt} {g' h' : (N.twist β u).Gt} (a : Mult β u t g g')
    (b : Mult β u t' h h') : Mult β u (fun z => t z * t' z) (g * h) (g' * h') := by
  refine ⟨congrArg₂ (fun x y : N.A => x * y) a.1 b.1, fun z => ?_⟩
  change g'.s z * h'.s z / N.θ (N.c z) g'.b h'.b = g.s z * h.s z / N.θ (N.c z) g.b h.b * (t z * t' z)
  rw [a.1, b.1, a.2, b.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem Mult.pow {t : N.X → Oˣ} {g : N.Gt} {g' : (N.twist β u).Gt} (a : Mult β u t g g') (n : ℕ) :
    Mult β u (fun z => t z ^ n) (g ^ n) (g' ^ n) := by
  induction n with
  | zero => exact ⟨rfl, fun z => by simp only [pow_zero, _root_.mul_one]; rfl⟩
  | succ n ih => simp only [pow_succ]; exact ih.mul a

theorem qEq_of_twRel {s : Oˣ} {j : ℕ} (hs : s ^ j = u) {p p' : N.QT j} {P P' : (N.twist β u).QT j}
    (a : TwRel β u s p P) (b : TwRel β u s p' P') (h : N.QEq p p') : (N.twist β u).QEq P P' := by
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, ?_⟩
  · rw [a.1, b.1]; exact h1
  · have c : Mult β u (fun w => u ^ β.be z w) (N.io z) ((N.twist β u).io z) := ⟨rfl, fun w => N.twist_τ β u z w⟩
    have d := (show Mult β u (fun w => s ^ β.be p.1.1.toAdd w) p.1.2 P.1.2 from a.2).mul c
    refine NumD.Gt.ext (b.2.1.trans ((congrArg NumD.Gt.b h2).trans d.1.symm)) (funext fun (w : N.X) => ?_)
    refine (b.2.2 w).trans (Eq.trans ?_ (d.2 w).symm)
    rw [h2, h1, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, zpow_add, zpow_mul,
      zpow_natCast, hs]
end

theorem tx_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)}
    (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

theorem qEq_pow {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] {j : ℕ} (q : La → N.QT j)
    (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (x : La) (n : ℕ) : N.QEq (q x ^ (n + 1)) (q ((n + 1) • x)) := by
  have E : Equivalence (N.QEq (k := j)) := by
    constructor
    · intro p
      exact ⟨0, by simp, by simp⟩
    · rintro p p' ⟨z, h, h'⟩
      exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
    · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
      exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩
  have qmul : ∀ {p p' q q' : N.QT j}, N.QEq p p' → N.QEq q q' → N.QEq (p * q) (p' * q') := by
    intro p p' q q' ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
    refine ⟨z + w, ?_, ?_⟩
    · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
      rw [h1, h3, smul_add]; abel
    · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
      rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _
  induction n with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ n ih =>
    rw [pow_succ, succ_nsmul x (n + 1)]
    exact E.trans (qmul ih (E.refl _)) (hq _ _)
end GlobalTheory.Ex.TwNest

namespace GlobalTheory.Ex

open TwNest in
theorem twist_tx_nest : ∀ (C : Type) [NormedField C] (N : NumD C) (La : Type) [AddCommGroup La] (q : ∀ n : ℕ, La → N.QT n), (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) → (∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a)) → ∀ (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → ∀ (n m : ℕ), Odd n → Odd m → ∀ (x : La) (p'' : (N.twist β u).QT ((n * m) ^ 2)) (p : (N.twist β u).QT (m ^ 2)), TwRel β u (r ((n * m) ^ 2)) (q _ (n • x)) p'' → TwRel β u (r (m ^ 2)) (q _ x) p → (N.twist β u).tx (n * m) p'' = (N.twist β u).tx m p := by
  intro C _ N La _ q hadd htow k β u r hr n m hn hm x p'' p h'' h
  have hK : (n * m) ^ 2 = m ^ 2 * n ^ 2 := by ring
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have hK0 : 0 < (n * m) ^ 2 := pow_pos (hn.mul hm).pos 2
  have hρ : r ((n * m) ^ 2) ^ (n ^ 2) = r (m ^ 2) := by rw [hK]; exact hr.2 _ _ hm2 hn2
  have htow' : ∀ K, K = m ^ 2 * n ^ 2 → ∀ p : N.QT (m ^ 2), p.1.1 = (q K x).1.1 → p.1.2 = (q K x).1.2 ^ (n ^ 2) →
      N.QEq p (q (m ^ 2) x) := by
    rintro _ rfl; exact htow _ _ hm2 hn2 x
  set Y := q ((n * m) ^ 2) x with hY
  obtain ⟨P, hP, -⟩ := existsUnique_twRel β u _ (hr.pow hK0) Y
  have hPm : Mult β u (fun w => r ((n * m) ^ 2) ^ β.be Y.1.1.toAdd w) Y.1.2 P.1.2 := hP.2
  let Y' : N.QT (m ^ 2) := ⟨(Y.1.1, Y.1.2 ^ (n ^ 2)), by
    change (Y.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact Y.2⟩
  let P' : (N.twist β u).QT (m ^ 2) := ⟨(P.1.1, P.1.2 ^ (n ^ 2)), by
    change (P.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact P.2⟩
  have t1 : TwRel β u (r (m ^ 2)) Y' P' := ⟨hP.1, (hPm.pow (n ^ 2)).1, fun w => ((hPm.pow (n ^ 2)).2 w).trans (by
    change (Y.1.2 ^ (n ^ 2)).s w * (_ ^ β.be Y.1.1.toAdd w) ^ (n ^ 2) = (Y.1.2 ^ (n ^ 2)).s w * _ ^ β.be Y.1.1.toAdd w
    rw [← hρ, ← zpow_natCast (_ ^ β.be _ _), ← zpow_natCast (r _), ← zpow_mul, ← zpow_mul, mul_comm (β.be _ _)])⟩
  have t2 : TwRel β u (r ((n * m) ^ 2)) (Y ^ n) (P ^ n) := ⟨congrArg (fun y : Multiplicative N.X => y ^ n) hP.1,
    (hPm.pow n).1, fun w => ((hPm.pow n).2 w).trans (by
      change _ = (Y.1.2 ^ n).s w * _ ^ β.be (n • Y.1.1.toAdd) w
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, mul_comm (n : ℤ), zpow_mul, zpow_natCast])⟩
  have e1 : N.QEq Y' (q (m ^ 2) x) := htow' _ hK Y' rfl rfl
  have e2 : N.QEq (Y ^ n) (q ((n * m) ^ 2) (n • x)) := by
    have := qEq_pow N (q ((n * m) ^ 2)) (hadd _ hK0) x (n - 1)
    rwa [Nat.sub_add_cancel hn.pos] at this
  rw [tx_of_qEq _ (hn.mul hm) (qEq_of_twRel (hr.pow hK0) t2 h'' e2), tx_of_qEq _ hm (qEq_of_twRel (hr.pow hm2) t1 h e1)]
  refine tsum_congr fun χ => GlobalTheory.T.degenerationSeriesTerms_nest C _ n m hn hm (P ^ n) P' rfl ?_ χ
  change P.1.2 ^ (n ^ 2) = (P.1.2 ^ n) ^ n
  rw [← pow_mul, sq n]
end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxNestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_tx_nsmul_eq_of_odd : ∀ (C : Type) [NormedField C] (N : NumD C) (La : Type) [AddCommGroup La] (q : ∀ n : ℕ, La → N.QT n), (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) → (∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a)) → ∀ (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → ∀ (n m : ℕ), Odd n → Odd m → ∀ (x : La) (p'' : (N.twist β u).QT ((n * m) ^ 2)) (p : (N.twist β u).QT (m ^ 2)), TwRel β u (r ((n * m) ^ 2)) (q _ (n • x)) p'' → TwRel β u (r (m ^ 2)) (q _ x) p → (N.twist β u).tx (n * m) p'' = (N.twist β u).tx m p := by
  first | exact @GlobalTheory.Ex.twist_tx_nest | exact GlobalTheory.Ex.twist_tx_nest | (intros; apply GlobalTheory.Ex.twist_tx_nest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObject
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem ser_nested {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K] (S : Ser a K (algebraMap _ K))
    (r m : ℕ) (hr : Odd r) (hm : Odd m) : ∃ c : Kˣ, ∀ x, S.v (r * m) (r • x) = c * S.v m x := by
  obtain ⟨C, _, _, _, _, _, gam, u, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension O' K
  obtain ⟨A, ρ, -, -, hρ, hv⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hR : Roots u ρ := ⟨Units.ext ((hρ 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n k hn hk => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hρ, hρ, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n k hn hk])⟩
  obtain ⟨b₁, -, b₃, -, b₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₁, q₂⟩ := GlobalTheory.T.qval_add_of_tower E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q b₁ b₃
    (fun k => ⟨(b₅ k).1, (b₅ k).2.2⟩) A.hq
  have hrm : Odd (r * m) := hr.mul hm
  choose p hp _ using fun x => existsUnique_twRel A.be u (ρ (m ^ 2)) (hR.pow (pow_pos hm.pos 2)) (A.q _ x)
  choose p' hp' _ using fun x => existsUnique_twRel A.be u (ρ ((r * m) ^ 2)) (hR.pow (pow_pos hrm.pos 2)) (A.q _ x)
  obtain ⟨s, hs⟩ := (hv m hm p hp).1
  obtain ⟨s', hs'⟩ := (hv _ hrm p' hp').1
  have key : ∀ x, gam (S.v (r * m) (r • x)) = (s' * s⁻¹ : Cˣ) * gam (S.v m x) := fun x => by
    rw [hs, hs', GlobalTheory.T.twist_tx_nsmul_eq_of_odd C A.N D.La A.q q₁ q₂ _ A.be u ρ hR r m hr hm x _ _ (hp' _) (hp x), Units.val_mul,
      _root_.mul_assoc, Units.inv_mul_cancel_left]
  by_cases h : ∃ x, S.v m x ≠ 0
  · obtain ⟨x₀, h₀⟩ := h
    have e : gam (S.v (r * m) (r • x₀) / S.v m x₀) = (s' * s⁻¹ : Cˣ) := by
      rw [map_div₀, key, mul_div_cancel_right₀ _ ((map_ne_zero gam).2 h₀)]
    refine ⟨Units.mk0 (S.v (r * m) (r • x₀) / S.v m x₀) fun h => (s' * s⁻¹).ne_zero (by rw [← e, h, map_zero]),
      fun x => gam.injective ?_⟩
    rw [map_mul, Units.val_mk0, e, key]
  · simp only [not_exists, not_not] at h
    exact ⟨1, fun x => gam.injective (by rw [key, h, mul_zero, map_zero, mul_zero])⟩

theorem one_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro hV _ _ _ h₁ h₂ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ _ _ _ _ S n hn ho h
  exact exists_full_all hV.1.1 h₁ h₂ S.A.ρ S.A.I.ζ S.A.I.ζ_pow S.v (ser_nested S) hn ho h

end GlobalTheory.Ex.AllLevels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObjectStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_allPrimePowerLevels_of_single_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  first | exact @GlobalTheory.Ex.AllLevels.one_object | exact GlobalTheory.Ex.AllLevels.one_object | (intros; apply GlobalTheory.Ex.AllLevels.one_object <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ArcPoint

theorem spMap_cancel {V L K : Type} [CommRing V] [CommRing L] [CommRing K] {f : L →+* K} (hf : Function.Injective f)
    {x : Sp L ⟶ Sp V} {φ : V →+* L} (h : spMap f ≫ x = spMap (f.comp φ)) : x = spMap φ := by
  obtain ⟨α, rfl⟩ := Spec.map_surjective x
  have e : spMap (f.comp α.hom) = spMap (f.comp φ) := (spMap_comp' _ _).trans h
  have e' : f.comp α.hom = f.comp φ := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have e'' : α.hom = φ := RingHom.ext fun v => hf (RingHom.congr_fun e' v)
  rw [← e'']
  rfl

theorem exists_finite_factor {V K₀ K : Type} [CommRing V] [Field K₀] [Field K] [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K]
    {X : Scheme.{0}} (s : X ⟶ Sp V) [LocallyOfFiniteType s] (φ : V →+* K₀) (x : Sp K ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap K₀ K).comp φ)) :
    ∃ L : IntermediateField K₀ K, FiniteDimensional K₀ L ∧ ∃ x' : Sp L ⟶ X, spMap (algebraMap L K) ≫ x' = x ∧
      x' ≫ s = spMap ((algebraMap K₀ L).comp φ) := by
  obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues (pullback s (spMap φ)) K
    (pullback.lift x (spMap (algebraMap K₀ K)) (hx.trans (spMap_comp' _ _)))
  obtain ⟨L, hL, hE⟩ := h₃ K₀ (pullback.snd _ _) inferInstance (pullback.lift_snd _ _ _) inferInstance
  obtain ⟨y, hy⟩ := (h₂ L (algebraMap L K)).1 (fun z hz => ⟨⟨z, by rw [← hE] at hz; exact hz⟩, rfl⟩)
  have e : spMap (algebraMap L K) ≫ y ≫ pullback.fst _ _ = x := by rw [← Category.assoc, hy, pullback.lift_fst]
  refine ⟨L, hL, y ≫ pullback.fst _ _, e, spMap_cancel (f := algebraMap L K) (algebraMap L K).injective ?_⟩
  rw [← Category.assoc, e, hx]
  rfl

theorem exists_normal_order (A L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (g : A →+* R) (e : L ≃+* FractionRing R), Function.Injective g ∧ g.Finite ∧
      IsIntegrallyClosed R ∧ ∀ x, e (algebraMap (FractionRing A) L (algebraMap A _ x)) = algebraMap R _ (g x) := by
  letI : Algebra A L := ((algebraMap (FractionRing A) L).comp (algebraMap A _)).toAlgebra
  haveI : IsScalarTower A (FractionRing A) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A (FractionRing A) L _
  have hfin : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A (FractionRing A) L _
  refine ⟨integralClosure A L, inferInstance, inferInstance, algebraMap A _,
    (FractionRing.algEquiv (integralClosure A L) L).symm.toRingEquiv, fun x y h => ?_, hfin,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A), fun x => ?_⟩
  · exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective (congrArg Subtype.val h))
  · exact (FractionRing.algEquiv (integralClosure A L) L).symm.commutes (algebraMap A _ x)

theorem exists_extend {L K C : Type} [Field L] [Field K] [Algebra L K] [Algebra.IsAlgebraic L K] [Field C] [IsAlgClosed C]
    (f : L →+* C) : ∃ g : K →+* C, ∀ x, g (algebraMap L K x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : K →ₐ[L] C), fun x => (IsAlgClosed.lift : K →ₐ[L] C).commutes x⟩

theorem exists_extend_valuation {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (b : V →+* K) : ∃ f : F →+* K, ∀ x : V, f x = b x := by
  have hb : Function.Injective b := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have ha : IsAlgebraic ℤ (x : F) := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have ha' : IsAlgebraic ℤ x := (isAlgebraic_algHom_iff V.subtype.toIntAlgHom Subtype.val_injective).1 ha
    refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker b) h0 hx ha' (eq_bot_iff.2 fun n hn => ?_)
    simpa using hn
  exact ⟨IsFractionRing.lift hb, fun x => IsFractionRing.lift_algebraMap hb x⟩

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) : x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rwa [map_pow, pow_le_one_iff hn] at h

theorem exists_prime_unit (O : Type) [CommRing O] [IsLocalRing O] {d : ℕ} (hd : d ≠ 0) :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) ∧ ¬ n ∣ d := by
  obtain ⟨p, hp, pp⟩ := Nat.exists_infinite_primes (d + 3)
  obtain ⟨q, hq, qp⟩ := Nat.exists_infinite_primes (p + 1)
  have key : ∀ n : ℕ, n.Prime → d + 3 ≤ n → IsUnit (n : O) → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) ∧ ¬ n ∣ d :=
    fun n hn h hu => ⟨n, hn, hn.odd_of_ne_two (by omega), hu, fun h' => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) h'; omega⟩
  obtain ⟨a, b, hab⟩ : IsCoprime (p : O) (q : O) :=
    Nat.Coprime.cast ((Nat.coprime_primes pp qp).2 (by omega))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key p pp hp (isUnit_of_mul_isUnit_right h)
  · exact key q qp (by omega) (isUnit_of_mul_isUnit_right h)

theorem valuation_comap_eq_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') (S : ValuationSubring K') (x : K) :
    (S.comap f).valuation x = 1 ↔ S.valuation (f x) = 1 := by
  have key : ∀ {F : Type} [Field F] (T : ValuationSubring F) (y : F), T.valuation y = 1 ↔ y ≠ 0 ∧ y ∈ T ∧ y⁻¹ ∈ T := by
    intro F _ T y
    rw [← T.valuation_le_one_iff, ← T.valuation_le_one_iff, map_inv₀]
    constructor
    · intro h
      refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
      rw [h0, map_zero] at h
      exact zero_ne_one h
    · rintro ⟨h0, h₁, h₂⟩
      have : 0 < T.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 h0)
      exact le_antisymm h₁ ((inv_le_one₀ this).1 h₂)
  rw [key, key, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, map_ne_zero]

section
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem summable_txT (h : N.Int q) {m : ℕ} (hm : m ≠ 0) (p : N.QT (m ^ 2)) : Summable (N.txT m p) := by
  have hp : p.1.2 ^ m ^ 2 = N.io p.1.1.toAdd := p.2
  exact (summable_vt_QT C N q h m hm ⟨(p.1.1, p.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, ← sq, hp]⟩).mul_left _

theorem summable_evT (h : N.Int q) {m j : ℕ} (hm : m ≠ 0) (hj : j ≠ 0) (p : N.QT (m ^ 2)) (z : N.QT j) :
    Summable (N.evT m p z.1.2) := by
  have hp : p.1.2 ^ m ^ 2 = N.io p.1.1.toAdd := p.2
  have hz : z.1.2 ^ j = N.io z.1.1.toAdd := z.2
  refine (summable_vt_QT C N q h (m * j) (mul_ne_zero hm hj)
    ⟨(Multiplicative.ofAdd (m ^ 2 • z.1.1.toAdd + j • p.1.1.toAdd), (z.1.2 * p.1.2) ^ m), ?_⟩).mul_left _
  rw [NumD.mem_QT, toAdd_ofAdd, N.io_add, N.io_nsmul, N.io_nsmul, ← hp, ← hz, ← pow_mul, ← pow_mul, ← pow_mul, mul_pow]
  congr 2 <;> ring
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K] [CharZero K]

theorem coord_scale (hL : Laws) (o : Full D K) {m : ℕ} (hm : Odd m) {z : baseOver (Sp K) ⟶ o.P.A} {v v' : D.La → K}
    (s : Kˣ) (hs : ∀ x, v x = s * v' x) (h : o.Coord m z v) : o.Coord m z v' := by
  haveI := o.closed
  have hc := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K _ o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
    (o.I.ev (m ^ 2)) fun x => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨x, rfl⟩
  refine (hc.2.1 z _ _ h).2 ⟨s⁻¹, funext fun x => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Units.inv_mul_cancel_left]

theorem theta_scale (hL : Laws) (o : Full D K) {m : ℕ} (hm : Odd m) {v v' : D.La → K}
    (s : Kˣ) (hs : ∀ x, v x = s * v' x) (h : o.Theta m v) : o.Theta m v' := by
  haveI := o.closed
  have hc := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K _ o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
    (o.I.ev (m ^ 2)) fun x => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨x, rfl⟩
  exact (hc.2.2.1 _).2 (coord_scale hL o hm s hs ((hc.2.2.1 _).1 h))
end

theorem realises_of_has : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → AllA fun {_} _ _ _ {_} {D} {_} {_} {_} {_} _ {O'} _ _ {_} a =>
    ∀ (K : Type) [Field K] [CharZero K] [Algebra (FractionRing O') K] (i : PowerSeries O' →+* K) (S : Ser a K i) (o : Full D K),
      S.Has o → AllC (RingHom.id _) i fun {C} _ _ gam u => ∃ (A : Lift a C) (r : ℕ → Cˣ) (o' : Full D C),
        A.ν.IntN ∧ Roots u r ∧ FullExt gam o o' ∧ Realises o' A.arc A.be u r := by
  intro hV h6 hU hH hT hE hA E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ i S o ho C _ _ _ _ _ gam u h₁ h₂ h₃ h₄
  have hL := hV.1.1
  haveI := o.closed
  haveI : CharZero C := (RingHom.charZero_iff gam.injective).1 inferInstance
  obtain ⟨A, r, hint, ⟨-, hAρ, hAζ, -⟩, hr', hser⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hr : Roots u r := ⟨Units.ext ((hr' 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n m hn hm => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hr', hr', ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n m hn hm])⟩
  obtain ⟨o', hext, hθ, hco⟩ := GlobalTheory.T.fullTorsionPolarizedCMObject_extends_algClosed hV h6 hU hH hT hE hA E H D K C gam o
  have hO : CExt O' ⊥ C := ⟨fun x => by rw [h₁]; exact h₂ _, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  obtain ⟨q, hq, -⟩ := (UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hO A hint).2.2 u h₄
  refine ⟨A, r, o', hint, hr, hext, hr, ?_, fun n hn => Units.ext ?_, fun m hm p hp => ?_⟩
  · rw [hext.1, ho.1]; exact hAρ
  · rw [hext.2.1 n hn, ho.2.1 n hn]; exact hAζ n hn
  obtain ⟨⟨s, hs⟩, hw⟩ := hser m hm p hp
  refine ⟨fun x => summable_txT hq hm.pos.ne' _, theta_scale hL o' hm s hs (hθ _ _ (ho.2.2 m hm).1), fun j hj z t ht => ?_⟩
  obtain ⟨s', hs'⟩ := hw j hj z t ht
  exact ⟨fun x => summable_evT hq hm.pos.ne' hj.ne' _ _,
    coord_scale hL o' hm s' hs' (hco m j z _ hj ((ho.2.2 m hm).2 j hj z))⟩

theorem intFam_map {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {R R' K K' : Type}
    [CommRing R] [CommRing R'] [Field K] [Field K'] {u : R} {i : R →+* K} {s : ℕ} {v : D.La → K}
    (h : IntFam (D := D) u i s v) (g : R →+* R') (i' : R' →+* K') (f : K →+* K') (e : ∀ x, f (i x) = i' (g x)) :
    IntFam (D := D) (g u) i' s fun x => f (v x) := by
  intro S hS
  obtain ⟨h₁, h₂, h₃⟩ := h (S.comap f) fun r => by rw [ValuationSubring.mem_comap, e]; exact hS _
  simp only [valuation_comap_eq_one, e] at h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

theorem exists_point : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g ∧ g.Finite ∧ IsIntegrallyClosed R₁ ∧ y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ RealAt Y a g y₁ ∧ ThetaInt Y g y₁ := by
  intro hV h6 hU hH hT hE hA E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb
  have hloc : IsLocalRing O' ∧ IsPrincipalIdealRing O' := by
    rcases hb with h | h
    · letI := h.1.toField
      exact ⟨inferInstance, inferInstance⟩
    · haveI := h.1
      exact ⟨inferInstance, inferInstance⟩
  haveI := hloc.1
  haveI := hloc.2
  haveI : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  let K₀ := FractionRing (PowerSeries O')
  let K := AlgebraicClosure K₀
  haveI : FaithfulSMul (PowerSeries O') K := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
    IsFractionRing.injective (PowerSeries O') K₀ ((algebraMap K₀ K).injective h)
  haveI : Algebra.IsAlgebraic (PowerSeries O') K :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K₀)).2 inferInstance
  have hC : Function.Injective ((algebraMap (PowerSeries O') K).comp (PowerSeries.C (R := O'))) :=
    fun x y h => PowerSeries.C_injective (FaithfulSMul.algebraMap_injective (PowerSeries O') K h)
  letI : Algebra (FractionRing O') K := (IsFractionRing.lift hC).toAlgebra
  have hK : ∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x) :=
    fun x => IsFractionRing.lift_algebraMap hC x
  obtain ⟨S⟩ := GlobalTheory.T.exists_arcSeries_integral_algebraic_over_powerSeries hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK
  obtain ⟨n, hn, hodd, hu, hd⟩ := exists_prime_unit O' H.d_prime.ne_zero
  obtain ⟨o₀, hρ₀, h₀⟩ := GlobalTheory.T.thetaPoints_allPrimePowerLevels_of_single_object hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n hn hodd fun j hj =>
    GlobalTheory.T.exists_object_with_thetaPoint_of_degenerationSeries hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n j hn hodd hu hd hj
  obtain ⟨o, ho⟩ := GlobalTheory.T.power_series_algebraic_closure_compatible hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K hK S n hn hodd hu o₀ hρ₀ h₀
  haveI := c.fin
  obtain ⟨bF, hbF⟩ := exists_extend_valuation (c.V W₀)
    ((algebraMap (PowerSeries O') K₀).comp ((PowerSeries.C (R := O')).comp b))
  have hbK : ∀ x : c.V W₀, (algebraMap K₀ K).comp bF x = algebraMap (FractionRing O') K (algebraMap O' _ (b x)) :=
    fun x => by rw [hK, RingHom.comp_apply, hbF]; rfl
  obtain ⟨hpt, -, hext⟩ := GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hH hT hE hA E H D l Xo c W₀ Y K ((algebraMap K₀ K).comp bF)
  obtain ⟨y, ⟨hy, hfull⟩, -⟩ := hpt o (fun r hr => by
      have hm : r ∈ c.V W₀ := mem_of_pow_mem _ two_ne_zero (by
        have : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [hr] using H.sqrt_neg_disc_sq)
        rw [this]
        exact neg_mem (natCast_mem _ _))
      exact ho.1.trans ((S.A.ρ_eq ⟨r, hm⟩ hr).trans (hbK ⟨r, hm⟩).symm))
    (fun z hz => by
      have hm : z ∈ c.V W₀ := mem_of_pow_mem _ l.A_pos.ne' (by
        have : z ^ l.A = 1 := Subtype.ext (by
          simpa [hz, zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one)
        rw [this]
        exact one_mem _)
      rw [ho.2.1 _ l.A_pos]
      exact (S.A.ζ_eq ⟨z, hm⟩ hz).trans (hbK ⟨z, hm⟩).symm)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨L, hLf, y', hy', hy's⟩ := exists_finite_factor (pullback.snd Xo.s _) bF y hy
  obtain ⟨R₁, _, _, g, e, hgi, hgf, hRn, he⟩ := exists_normal_order (PowerSeries O') L
  have hover : (spMap (e : L →+* FractionRing R₁) ≫ y') ≫ Y.j ≫ Y.s =
      jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have e₁ : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W₀).subtype := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [e₁, Category.assoc, ← Category.assoc y', hy's, ← spMap_comp', ← spMap_comp', ← spMap_comp', ← spMap_comp']
    refine Eq.trans (congrArg spMap (RingHom.ext fun x => ?_)) (spMap_comp' _ (algebraMap R₁ _))
    exact (congrArg (fun t => e (algebraMap K₀ L t)) (hbF x)).trans (he _)
  have hx : ∀ (C : Type) [Field C] [IsAlgClosed C] (gam : FractionRing R₁ →+* C), ∃ f : K →+* C,
      spMap f ≫ y = spMap gam ≫ spMap (e : L →+* FractionRing R₁) ≫ y' ∧
      ∀ x, f (algebraMap (PowerSeries O') K x) = gam (algebraMap R₁ _ (g x)) := by
    intro C _ _ gam
    obtain ⟨f, hf⟩ := exists_extend (K := K) (gam.comp (e : L →+* FractionRing R₁))
    refine ⟨f, ?_, fun x => ?_⟩
    · rw [← hy', ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
      exact congrArg (fun t => spMap t ≫ y') (RingHom.ext hf)
    · rw [← he]
      exact hf (algebraMap K₀ L (algebraMap _ K₀ x))
  refine ⟨R₁, inferInstance, inferInstance, g, _, hgi, hgf, hRn, hover, ⟨⟨hgi, hgf, hover⟩, ?_⟩, ?_⟩
  · intro C _ _ _ _ _ gam u h₁ h₂ h₃ h₄
    obtain ⟨f, hf, hf'⟩ := hx C gam
    obtain ⟨A, r, o', p₁, p₂, p₃, p₄⟩ := realises_of_has hV h6 hU hH hT hE hA E H D l Xo c W₀ Y O' b ϖ a hb K _ S o ho C f u
      (fun x => (h₁ x).trans (hf' _).symm) (fun x => by rw [hf']; exact h₂ _) (h₃.trans (hf' _).symm) h₄
    exact ⟨A, r, o', p₁, p₂, hf ▸ hext C f y o o' hfull p₃, p₄⟩
  · obtain ⟨f, hf, hf'⟩ := hx (AlgebraicClosure (FractionRing R₁)) (algebraMap _ _)
    obtain ⟨o', p₁, p₂, -⟩ := GlobalTheory.T.fullTorsionPolarizedCMObject_extends_algClosed hV h6 hU hH hT hE hA E H D K _ f o
    exact ⟨o', hf ▸ hext _ f y o o' hfull p₁, fun n j hn ho' hu hj =>
      ⟨_, p₂ _ _ (ho.2.2 _ ho'.pow).1, intFam_map (S.int n j hn ho' hu hj) g _ f hf'⟩⟩

end GlobalTheory.ArcPoint

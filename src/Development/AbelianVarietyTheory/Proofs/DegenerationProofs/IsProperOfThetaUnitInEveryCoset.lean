module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosureStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCoset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.CosetGood

theorem subsingleton_of_forall_hom {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : n.Prime)
    (h : ∀ (l : X →+ ZMod n) (y : X), l y = 0) : Subsingleton X := by
  haveI : Fact n.Prime := ⟨hn⟩
  let b := Module.Free.chooseBasis ℤ X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    have := h ((Int.castAddHom (ZMod n)).comp (b.coord i).toAddMonoidHom) (b i)
    simp at this⟩
  exact b.repr.toEquiv.subsingleton

theorem subsingleton_of_labels {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] (N : NumD C) (Q : QuadraticMap ℤ N.X ℝ) (hQ : N.Int Q) {n g j : ℕ} (hn : n.Prime) (ho : Odd n)
    (h1 : ‖(n : C)‖ = 1) (hT : N.Tors n g) (hj : 2 ≤ j) {La : Type} [AddCommGroup La]
    (r : N.QT ((n ^ j) ^ 2) → La → Prop) (tot : ∀ a, ∃ q, r q a) (cot : ∀ q, ∃ a, r q a)
    (mul : ∀ q q' a a', r q a → r q' a' → r (q * q') (a + a')) (inj : ∀ q q' a, r q a → r q' a → N.QEq q q')
    (v : La → C) (hv : ∀ q : La → N.QT ((n ^ j) ^ 2), (∀ a, r (q a) a) → ∃ c : C, ∀ a, v a = c * N.tx (n ^ j) (q a))
    (hle : ∀ a, ‖v a‖ ≤ 1) (hco : ∀ a, ∃ h, ‖v (a + n ^ (j - 1) • h)‖ = 1) : Subsingleton N.X := by
  classical
  obtain ⟨hA, hB, -⟩ := GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N Q hQ n g hn ho h1 hT j (by omega)
  obtain ⟨q₀, -, -, hq₀⟩ := hB 1 rfl
  obtain ⟨a₀, ha₀⟩ := cot (1 * q₀)
  have tot' : ∀ a, ∃ q, r q a ∧ (a = a₀ → q = 1 * q₀) := fun a => by
    by_cases e : a = a₀
    · exact ⟨_, e ▸ ha₀, fun _ => rfl⟩
    · obtain ⟨q, hq⟩ := tot a
      exact ⟨q, hq, fun e' => absurd e' e⟩
  choose q hq hq' using tot'
  obtain ⟨c, hc⟩ := hv q hq
  have c1 : ‖c‖ ≤ 1 := by
    have := hle a₀
    rwa [hc, hq' a₀ rfl, norm_mul, hq₀, _root_.mul_one] at this
  have hu : ∀ a, ‖v a‖ = 1 → ‖N.tx (n ^ j) (q a)‖ = 1 := fun a ha => by
    rw [hc, norm_mul] at ha
    have := (hA (q a)).1
    nlinarith [norm_nonneg c, norm_nonneg (N.tx (n ^ j) (q a))]
  refine subsingleton_of_forall_hom hn fun l y => ?_
  have hl : ∀ (i : ℕ) (z : N.X), i ≠ 0 → l (n ^ i • z) = 0 := fun i z hi => by
    rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow hi, zero_mul]
  have he : ∀ p p' : N.QT ((n ^ j) ^ 2), N.QEq p p' → l p'.1.1.toAdd = l p.1.1.toAdd := by
    rintro p p' ⟨z, hz, -⟩
    rw [hz, map_add (f := _), show (n ^ j) ^ 2 • z = n ^ (j * 2) • z by rw [pow_mul], hl _ _ (by omega), add_zero]
  let Y : La →+ ZMod n := AddMonoidHom.mk' (fun a => l (q a).1.1.toAdd) fun a a' =>
    (he _ _ (inj _ _ _ (mul _ _ _ _ (hq a) (hq a')) (hq (a + a')))).trans (map_add l _ _)
  have hY : ∀ a, Y a = 0 := fun a => by
    obtain ⟨h, hh⟩ := hco a
    obtain ⟨z, hz⟩ := (hA _).2 (hu _ hh)
    have e : Y (a + n ^ (j - 1) • h) = 0 := (congrArg l hz).trans (hl _ _ (by omega))
    rwa [map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_mul,
      add_zero] at e
  have hn0 : (n : C) ≠ 0 := fun e => by rw [e, norm_zero] at h1; exact zero_ne_one h1
  have hs := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn0 hT (j * 2)).2.2.1 y
  rw [pow_mul] at hs
  obtain ⟨p, rfl⟩ := hs
  obtain ⟨a, ha⟩ := cot p
  exact (he _ _ (inj _ _ _ (hq a) ha)).trans (hY a)

theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    rfl⟩

theorem subsingleton_lattice (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    (o : Full D C) (M : Mdl o) {n j : ℕ} (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hj : 2 ≤ j) (v : D.La → C)
    (hv : o.Theta (n ^ j) v) (hle : ∀ x, ‖v x‖ ≤ 1) (hco : ∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) :
    Subsingleton M.P.D.toPre.X := by
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  have hR : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hev := M.P.D.psi_even
  have hbi := M.P.D.tau_bimult
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values hL M.W M.P.D.toPre hev hbi C S
    fun r => (hS _).2 (M.ext.1 r)
  have hI : ν.IntN := ⟨S, hS, hν⟩
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase M.W _ hR M.P.D C M.ext N ν hI
  have hT := GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) M.W M.P.D.toPre hev hbi C
    ⟨M.ext.1, fun r hr => M.ext.2 r (bot_le (a := IsLocalRing.maximalIdeal M.W) hr)⟩ N ν hI n hn ho h1
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values M.W M.P.D.toPre hev hbi C N ν
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  obtain ⟨g₆, g₇, g₈⟩ := g₅ ((n ^ j) ^ 2)
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hV.1 M.W _ hR M.P.D M.P.A M.t.G M.t.semi M.P.U C _ hk
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback M.cart (𝟙 (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun a => e (o.I.ev ((n ^ j) ^ 2) a)
  have hp : ∀ a, o.I.ev ((n ^ j) ^ 2) a ^ (n ^ j) ^ 2 = 1 := fun a => (o.I.onto _ hk _).2 ⟨a, rfl⟩
  have hx : ∀ a, x a ^ (n ^ j) ^ 2 = 1 := fun a => (map_pow e _ _).symm.trans ((congrArg e (hp a)).trans (map_one e))
  have hv' : IsThetaPt M.P.A (n ^ j) x fun a => fnOf (v a) := by
    have key : ∀ (s : Sp C ⟶ (TK M.W).left) (_ : s = 𝟙 _ ≫ jFK (R := M.W) C) (y : D.La → (Over.mk s ⟶ M.P.A.A)),
        (∀ a, (y a).left = (o.I.ev ((n ^ j) ^ 2) a).left ≫ M.φ) → IsThetaPt M.P.A (n ^ j) y fun a => fnOf (v a) := by
      rintro s rfl y hy
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp C)) M.cart M.lb hy hp _).1 hv
    exact key _ (Category.id_comp _).symm x fun a => he _
  have hm : ((n ^ j : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (pow_pos hn.pos _).ne'
  obtain ⟨-, c₂, c₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ M.P.A (jFK (R := M.W) C) (n ^ j) ho.pow hm D.La x hx
  haveI := subsingleton_of_labels N Q hQ hn ho h1 hT hj (fun q a => ∃ p, ν.QPt p q ∧ f p = x a) (fun a => ?_)
    (fun q => ?_) ?_ ?_ v (fun q hq => ?_) hle hco
  · exact ν.eX.symm.toEquiv.subsingleton
  · obtain ⟨p, hp⟩ := f₂ _ (hx a)
    obtain ⟨q, hq, -⟩ := g₆ p
    exact ⟨q, p, hq, hp⟩
  · obtain ⟨p, hp⟩ := g₇ q
    obtain ⟨w, hw⟩ := M.P.U.toUnifPre.ext
    have h₀ : f p ^ (n ^ j) ^ 2 = 1 := ((f₁ p (f p)).2 rfl w hw).1
    obtain ⟨a, ha⟩ := (o.I.onto _ hk (e.symm (f p))).1
      ((map_pow e.symm _ _).symm.trans ((congrArg e.symm h₀).trans (map_one e.symm)))
    exact ⟨a, p, hp, ((congrArg e ha).trans (e.apply_symm_apply _)).symm⟩
  · rintro q q' a a' ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    obtain ⟨p'', hp''⟩ := g₇ (q * q')
    refine ⟨p'', hp'', (f₄ p p' p'' ⟨p'', ?_, (g₃ _ _ _ _ _ _ hp.2 hp'.2 hp''.2).2 rfl, qk_equiv_refl hbi _⟩).trans ?_⟩
    · rw [← hp''.1, ← hp.1, ← hp'.1, ← map_add (f := _)]; rfl
    · rw [e₁, e₂]
      exact ((congrArg e (o.I.add _ a a')).trans (map_mul e _ _)).symm
  · rintro q q' a ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    exact (g₈ p p' q q' hp hp').1 ((f₃ p p').1 (e₁.trans e₂.symm))
  · choose p hp hp' using hq
    have ht := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL2) M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext
      N ν (n ^ j) ho.pow D.La p q x (fun a => (f₁ _ _).2 (hp' a).symm) hp
    obtain ⟨c, hc⟩ := (c₂ 1 _ v ((c₃ _).1 ht)).1 ((c₃ _).1 hv')
    exact ⟨c, fun a => congrFun hc a⟩

theorem isProper_of_unit_in_cosets : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  intro hV _ _ _ _ _ _ E _ _ _ H D C _ _ _ _ _ o M n j hn ho h1 hj v hv hle hco
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  exact (isAbelianScheme_of_unif_of_subsingleton hV.1.1 hV.1.2.1 M.W hcomp M.P.D M.P.A M.t.G M.t.semi M.P.U
    (subsingleton_lattice hV o M hn ho h1 hj v hv hle hco)).proper

end GlobalTheory.CosetGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCosetStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_theta_unit_in_every_coset : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  first | exact @GlobalTheory.CosetGood.isProper_of_unit_in_cosets | exact GlobalTheory.CosetGood.isProper_of_unit_in_cosets | (intros; apply GlobalTheory.CosetGood.isProper_of_unit_in_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TripleOut

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem exists_secOn_of_pow_one {X : Scheme.{0}} (L : LB X) (V : X.Opens)
    {σ : ∀ j, Γ(X, V ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j)}
    (hσ : σ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V) :
    ∃ θ ∈ secOn L V, ∀ j, X.basicOpen (σ j) ≤ X.basicOpen (θ (j 0)) := by
  have h : ∀ i, L.U i ≤ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U fun _ => i :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  refine ⟨fun i => resG X (inf_le_inf_left V (h i)) (σ fun _ => i), fun i j => ?_, fun j => ?_⟩
  · have e := congrArg (resG X (inf_le_inf (inf_le_inf_left V (h i)) (h j))) (hσ (fun _ => i) (fun _ => j))
    rw [map_mul, rr, rr, rr] at e
    rw [rr, rr, e]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_one]
    exact rr _ _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    intro x hx
    rw [Scheme.basicOpen_res]
    exact ⟨inf_le_inf_left V (LB.wchart_le L _ _ 0) (X.basicOpen_le _ hx), hx⟩

theorem mem_basicOpen_of_valF {K : Type} [Field K] {X : Scheme.{0}} (g : Sp K ⟶ X) {U : X.Opens} (f : Γ(X, U))
    (h : valF g U f ≠ 0) (w : Sp K) : g w ∈ X.basicOpen f :=
  (GlobalTheory.Points.le_preimage_basicOpen_iff g (by_contra fun hn => h (dif_neg hn)) f).2 (isUnit_iff_ne_zero.2 h)
    (x := w) trivial

theorem exists_geomPoint {X : Scheme.{0}} (y : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ X), ∀ w, x w = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun w => by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem hasTheta (Z : ZHOut ρ M U₀ EE) (h : M.HasDiv S.th) : GlobalTheory.Models.HasTheta Z.G Z.L.L := by
  intro z
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x₀, hx₀⟩ := h z
  let W : M.Z.Opens := ⟨_, M.isOpen_setOf_div S.th x₀⟩
  obtain ⟨σ, hσ, -, hne⟩ := Z.theta W x₀ fun _ hz => hz
  obtain ⟨θ, hθ, hle⟩ := exists_secOn_of_pow_one Z.L.L _ hσ
  refine ⟨W, hx₀, θ, hθ, fun y hy => ?_⟩
  obtain ⟨K, _, _, x, hx⟩ := exists_geomPoint y
  obtain ⟨g, j, hg, hv⟩ := hne K x (by rintro _ ⟨w, rfl⟩; rw [hx]; exact hy)
  refine ⟨g (IsLocalRing.closedPoint K), j 0, ?_, hle j ?_⟩
  · exact (Scheme.Hom.comp_apply g Z.G.hom _).symm.trans (hg ▸ hx _)
  · exact mem_basicOpen_of_valF g (σ j) hv _

theorem splitFib (Z : ZHOut ρ M U₀ EE) : GlobalTheory.Models.SplitFib Z.G := by
  intro z
  refine ⟨M.Z.residueField z, inferInstance, Algebra.id _, inferInstance, inferInstance, ?_⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap (M.Z.residueField z) (M.Z.residueField z))) ≫
      M.Z.fromSpecResidueField z = M.Z.fromSpecResidueField z := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h : ∀ f : Sp (M.Z.residueField z) ⟶ M.Z, f = M.Z.fromSpecResidueField z →
      ∃ E : SplitExt (Sp (M.Z.residueField z)), E.IsGt ((Over.pullback f).obj Z.G) := by
    rintro _ rfl
    exact Z.split z
  exact h _ e

section Cube

variable {B U X : Scheme.{0}} {A : Over B} {A' : Over U} {G : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj A']
  [IsCommMonObj A'] [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem pushPt_comp {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) {T : Over U} (x : T ⟶ A') : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem adj_pull {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' b' : A' ⟶ A'} {a b : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (hb : b'.left ≫ p = p ≫ b.left) (c : Pic A.left)
    (H : cubeCls ![fst A A ≫ a, snd A A] c = cubeCls ![fst A A, snd A A ≫ b] c) {T : Over U} (y₁ y₂ : T ⟶ A') :
    cubeCls ![y₁ ≫ a', y₂] (pull p c) = cubeCls ![y₁, y₂ ≫ b'] (pull p c) := by
  let v := lift (pushPt h.1.w y₁) (pushPt h.1.w y₂)
  refine (pull_cubeCls_push h _ _ v (fun i => ?_) c).symm.trans
    ((congrArg (pull v.left) H).trans (pull_cubeCls_push h _ _ v (fun i => ?_) c))
  · fin_cases i
    · exact (pushPt_comp h ha _).trans (by simp [v])
    · simp [v]
  · fin_cases i
    · simp [v]
    · exact (pushPt_comp h hb _).trans (by simp [v])

theorem pull_graph {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (c : Pic A.left) :
    pull p (cubeCls ![𝟙 A, a] c) = cubeCls ![𝟙 A', a'] (pull p c) := by
  have h₁ := pull_cubeCls_push h ![𝟙 A', a'] ![𝟙 A, a] (pushPt h.1.w (𝟙 A'))
    (fun i => by
      fin_cases i
      · simp
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h ha _)) c
  have e : (pushPt h.1.w (𝟙 A')).left = p := Category.id_comp _
  rwa [e] at h₁

variable [IsIntegral X] [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) [Nonempty U] {j : U ⟶ X}
  [IsOpenImmersion j] (semi : IsSemiAbelian G) {φ : A'.left ⟶ G.left} (h : IsGrpPullback A' G j φ)
include hX semi h

theorem adj_extend {a' b' : A' ⟶ A'} {a b : G ⟶ G} [IsMonHom a] [IsMonHom b]
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) (c : Pic G.left)
    (H : ∀ {T : Over U} (y₁ y₂ : T ⟶ A'), cubeCls ![y₁ ≫ a', y₂] (pull φ c) = cubeCls ![y₁, y₂ ≫ b'] (pull φ c)) :
    cubeCls ![fst G G ≫ a, snd G G] c = cubeCls ![fst G G, snd G G ≫ b] c := by
  have := semi.smooth
  have := semi.geomConnected
  have hsm : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
  let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
  have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ A', pushPt h.1.w y' = u ≫ y := fun y =>
    ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨y₁, hy₁⟩ := hy (fst G G)
  obtain ⟨y₂, hy₂⟩ := hy (snd G G)
  let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
  refine pic_ext X hX j (G ⊗ G).hom e.left u.left T'.hom hsm
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
    (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
  · refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
      ((H y₁ y₂).trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
    · fin_cases i
      · simp [pushPt_comp h ha, hy₁]
      · simp [hy₂]
    · fin_cases i
      · simp [hy₁]
      · simp [pushPt_comp h hb, hy₂]
  · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
    congr 1
    funext i
    fin_cases i <;> simp [e]

theorem prim_extend {a' : A' ⟶ A'} {a : G ⟶ G} [IsMonHom a] (ha : a'.left ≫ φ = φ ≫ a.left) (c : Pic G.left)
    (hc : pull (eSec G) c = 0) (H : pull φ c = cubeCls ![𝟙 A', a'] (pull φ c)) : c = cubeCls ![𝟙 G, a] c := by
  have := semi.smooth
  have := semi.geomConnected
  refine pic_ext X hX j G.hom (eSec G) φ A'.hom inferInstance
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _
    (H.trans (pull_graph h ha c).symm) ?_
  refine hc.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
  refine (cubeCls_one (n := 2) _ hc).symm.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp

end Cube

theorem exists_triple : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (act : OAct (NumberField.RingOfIntegers E) ρ.P.A), S.Over₀ M U₀ → (∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L) → ∃ (act' : OAct (NumberField.RingOfIntegers E) Z.G) (h₂ : _) (h₃ : _), (∀ a, ((Over.pullback Z.u₀).map (act.act a)).left ≫ Z.φ = Z.φ ≫ (act'.act a).left) ∧ (GlobalTheory.Models.AbOpen Z.G → GlobalTheory.Models.Good (SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃)) := by
  intro hD o Ω _ _ _ _ S ρ M U₀ EE Z E _ _ _ H act hO hadj hprim
  have := (inferInstance : ArithBase o Ω).ft
  have := (inferInstance : ArithBase o Ω).char
  have := M.locallyOfFiniteType_int
  have hfl := M.flat_int (M.s ≫ spMap (algebraMap ℤ o))
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian (M.s ≫ spMap (algebraMap ℤ o))
  have := ρ.P.isAb.comm
  have : Nonempty U₀.toScheme := hO.ne.to_subtype
  have hd : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨_, _⟩ := ExtUnique.dense_open U₀ hd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian Z.G Z.semi
  let act₀ := Geo.Tor.OAct.pullback Z.u₀ ρ.P.A act
  obtain ⟨act', hact, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback Z.cart act₀ fun x => by
    obtain ⟨e, he, he'⟩ := grpPullback_iso Z.cart (isGrpPullback_pullback Z.G U₀.ι)
    have := act₀.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hD M.Z U₀ U₀.ι ⟨hO.normal, _, inferInstance, hfl⟩ inferInstance inferInstance
      inferInstance inferInstance Z.G Z.G Z.semi Z.semi (e.inv ≫ act₀.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    rw [← he', Category.assoc, ← ExtUnique.pullback_map_left_fst, hF, ← Category.assoc, ← Category.assoc,
      ← Over.comp_left, ← Over.comp_left, Iso.hom_inv_id_assoc]
  have hp := isGrpPullback_pullback ρ.P.A Z.u₀
  have ha : ∀ x, (act₀.act x).left ≫ pullback.fst ρ.P.A.hom Z.u₀ = pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act x).left :=
    fun x => ExtUnique.pullback_map_left_fst _ _
  have hc : pull Z.φ (cls Z.L.L Z.L.isLB) = pull (pullback.fst ρ.P.A.hom Z.u₀) (cls ρ.P.L ρ.P.isLB) :=
    (cls_eq_iff (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _)).2 ⟨Z.w, Z.w_gen⟩
  refine ⟨act', fun b => ?_, ?_, hact, fun h => ⟨h, splitFib Z, hasTheta Z hO.div⟩⟩
  · refine (cls_eq_iff (isLB_cube _ Z.L.isLB) (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB, cls_cube _ Z.L.isLB]
    have := act'.hom b
    have := act'.hom (H.bar b)
    have h₀ := (cls_eq_iff (isLB_cube _ ρ.P.isLB) (isLB_cube _ ρ.P.isLB)).2 (hadj b)
    rw [cls_cube _ ρ.P.isLB, cls_cube _ ρ.P.isLB] at h₀
    refine adj_extend hO.normal Z.semi Z.cart (hact b) (hact (H.bar b)) _ fun y₁ y₂ => ?_
    rw [hc]
    exact adj_pull hp (ha b) (ha (H.bar b)) _ h₀ y₁ y₂
  · refine (cls_eq_iff Z.L.isLB (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB]
    have := act'.hom H.w0
    have h₀ := (cls_eq_iff ρ.P.isLB (isLB_cube _ ρ.P.isLB)).2 hprim
    rw [cls_cube _ ρ.P.isLB] at h₀
    refine prim_extend hO.normal Z.semi Z.cart (hact H.w0) _
      ((cls_eq_zero_iff (pull_isLB Z.L.isLB _)).2 ⟨Z.L.rig, Z.L.rigGen⟩) ?_
    rw [hc]
    exact (congrArg (pull _) h₀).trans (pull_graph hp (ha H.w0) _)

end GlobalTheory.TripleOut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosureGroup

theorem exists_rescale {X' S' X S Y T : Scheme.{0}} (π : X' ⟶ S') (e' : S' ⟶ X') (he : e' ≫ π = 𝟙 S')
    (F : X' ⟶ X) (f : S' ⟶ S) (e : S ⟶ X) (hF : e' ≫ F = f ≫ e)
    (F₂ : X' ⟶ Y) (f₂ : S' ⟶ T) (e₂ : T ⟶ Y) (hF₂ : e' ≫ F₂ = f₂ ≫ e₂)
    {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (a : LB.Gen (L.pull e)) (ha : a.IsGen)
    (b : LB.Gen (M.pull e₂)) (hb : b.IsGen) (H : LBIso (M.pull F₂) (L.pull F)) :
    ∃ w : LB.Iso (M.pull F₂) (L.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (p : L.ι) (q : M.ι),
      F (e' (r z)) ∈ L.U p → F₂ (e' (r z)) ∈ M.U q →
      gm (r ≫ f) z ((L.pull e).U fun _ => p) (a.s fun _ => p) =
        gw w (r ≫ e') z p (fun _ => q) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => q) (b.s fun _ => q) := by
  obtain ⟨w, hw⟩ := H
  have pg := (isGen_iff w).1 hw
  have m₁ : ∀ (s : S') (p : L.ι), F (e' s) ∈ L.U p → f s ∈ (L.pull e).U fun _ => p := fun s p h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ L.U p) hF).mp h)
  have m₂ : ∀ (s : S') (q : M.ι), F₂ (e' s) ∈ M.U q → f₂ s ∈ (M.pull e₂).U fun _ => q := fun s q h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ M.U q) hF₂).mp h)
  let W : L.ι × M.ι → S'.Opens := fun j =>
    e' ⁻¹ᵁ ((L.pull F).U (fun _ => j.1) ⊓ (M.pull F₂).U (fun _ => j.2))
  have l₁ : ∀ j, W j ≤ f ⁻¹ᵁ (L.pull e).U fun _ => j.1 := fun j s hs => m₁ s _ (mem_pull.1 hs.1)
  have l₂ : ∀ j, W j ≤ f₂ ⁻¹ᵁ (M.pull e₂).U fun _ => j.2 := fun j s hs => m₂ s _ (mem_pull.1 hs.2)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(S', W j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) j, r z ∈ W j →
      gm r z (W j) (u j) = gm (r ≫ f) z ((L.pull e).U fun _ => j.1) (a.s fun _ => j.1) *
        (gw w (r ≫ e') z j.1 (fun _ => j.2) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => j.2) (b.s fun _ => j.2))⁻¹ :=
    ⟨fun j => res (l₁ j) (pullU f _ (a.s fun _ => j.1)) *
      ((show Γ(S', W j)ˣ from pullU e' _ (w.s (fun _ => j.1, fun _ => j.2))) * res (l₂ j) (pullU f₂ _ (b.s fun _ => j.2)))⁻¹,
      fun Z r z j hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r f z _ (l₁ j hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          (gm_pull r e' z _ hz _) ((gm_res r z _ hz _).trans (gm_pull r f₂ z _ (l₂ j hz) _)))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun s _ => by
      obtain ⟨p, hp⟩ := exists_chart hL (F (e' s))
      obtain ⟨q, hq⟩ := exists_chart hM (F₂ (e' s))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), mem_pull.2 hp, mem_pull.2 hq⟩) u (fun i j s hs => by
    have e₁ := gen_trans ha (𝟙 S' ≫ f) s (l₁ i hs.1) (l₁ j hs.2)
    have e₂' := gen_trans hb (𝟙 S' ≫ f₂) s (l₂ i hs.1) (l₂ j hs.2)
    have e₃ := pg _ (𝟙 S' ≫ e') s i.1 j.1 (fun _ => i.2) (fun _ => j.2) (mem_pull.1 hs.1.1) (mem_pull.1 hs.2.1)
      hs.1.2 hs.2.2
    rw [gm_pull_g M F₂ (𝟙 S' ≫ e') s _ _ hs.1.2 hs.2.2] at e₃
    simp only [trF, Fintype.prod_unique, zpow_one, Category.id_comp, ← hF, ← hF₂] at e₁ e₂' e₃
    rw [hu _ _ s i hs.1, hu _ _ s j hs.2]
    simp only [Category.id_comp]
    have alg : ∀ {V : Type} [CommGroup V] (A B x y z x' y' z' : V), x' = A * x → z' = B * z → y' = A * B⁻¹ * y →
        x' * (y' * z')⁻¹ = x * (y * z)⁻¹ := by
      rintro V _ A B x y z _ _ _ rfl rfl rfl
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact alg _ _ _ _ _ _ _ _ e₁ e₂' e₃)
  have hv : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (V : X'.Opens), g z ∈ V →
      gm g z V (res (le_top : V ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c)) = gm (g ≫ π) z ⊤ c := fun Z g z V h =>
    (gm_res g z _ h _).trans (gm_pull g π z ⊤ trivial c)
  let w' : LB.Iso (M.pull F₂) (L.pull F) := ⟨fun j => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s j⟩
  have hw' : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (p : L.ι) (q), F (g z) ∈ L.U p → g z ∈ (M.pull F₂).U q →
      gw w' g z p q = gm (g ≫ π) z ⊤ c * gw w g z p q := fun Z g z p q hp hq =>
    (map_mul _ _ _).trans (congrArg (· * _) (hv Z g z _ ⟨mem_pull.2 hp, hq⟩))
  refine ⟨w', (isGen_iff w').2 fun Z g z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw' Z g z j k hj hk, hw' Z g z j' k' hj' hk', pg Z g z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (p, q) := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have e₁ := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hu Z r z (p, q) hz))
    rw [hw' Z (r ≫ e') z p _ hp (mem_pull.2 hq), Category.assoc, he, Category.comp_id, e₁, _root_.mul_assoc,
      inv_mul_cancel_right]

theorem isSymmetric_of_pull (hG : GlobalFnsSt) {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Sym A L) (L' : RigLB A') (H : LBIso L'.L (L.pull φ)) : L'.IsSymmetric := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG hA hL hs
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullSame L (K := Fin 2)
    (fun k => (![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] : Fin 2 → _) k ≫ φ) _ ![1, -1] φ fun k => by
      fin_cases k
      · exact PolBaseChange.inv_comm h
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) u hu
  exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L' (exists_down ((isGen_iff w).1 hw) hL L'.isLB t ht)

theorem isQProjOver_ι {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) (U : X.Opens)
    [QuasiCompact U.ι] : IsQProjOver (U.ι ≫ f) := by
  obtain ⟨N, i, hi, e⟩ := h
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [Category.assoc, e]⟩

theorem valF_eq_mul_of_gm {K : Type} [Field K] {X₁ X₂ X₃ : Scheme.{0}} {x₁ : Sp K ⟶ X₁} {x₂ : Sp K ⟶ X₂}
    {x₃ : Sp K ⟶ X₃} {U₁ : X₁.Opens} {U₂ : X₂.Opens} {U₃ : X₃.Opens} (z : Sp K) (h₁ : x₁ z ∈ U₁) (h₂ : x₂ z ∈ U₂)
    (h₃ : x₃ z ∈ U₃) {u₁ : Γ(X₁, U₁)ˣ} {u₂ : Γ(X₂, U₂)ˣ} {u₃ : Γ(X₃, U₃)ˣ}
    (e : gm x₁ z U₁ u₁ = gm x₂ z U₂ u₂ * gm x₃ z U₃ u₃) :
    valF x₁ U₁ u₁.val = valF x₂ U₂ u₂.val * valF x₃ U₃ u₃.val :=
  (toStk z).injective (by
    rw [map_mul, toStk_valF x₁ U₁ z h₁, toStk_valF x₂ U₂ z h₂, toStk_valF x₃ U₃ z h₃, e, Units.val_mul])

theorem exists_pre : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ M U₀ EE Q ex hbig htest hind hch htors ⟨T, hT⟩
  have hcomm : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  have gp : IsGrpPullback ex.core.A ρ.P.A Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨-, hamp, hK⟩ := GlobalTheory.pol_pull _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB ρ.P.isAb gp hT
  have hsym : T.L.IsSymmetric := isSymmetric_of_pull hL.globalFns gp ρ.P.isAb ρ.P.isLB ρ.P.sym T.L hT
  have hS := GlobalTheory.SymBaseChange.hypS_baseChange _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB gp hT ρ.hypS
  have hN : 4 ≤ S.N := by
    have h2 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    nlinarith
  have hunit : IsUnit ((S.r * S.N : ℕ) : Γ(ex.core.Z, ⊤)) := by
    have h := S.unit.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rw [map_natCast] at h
    exact h
  have hfew : T.Few (S.r * S.N) := GlobalTheory.ZJ.theta_few hU hL hL2 ex.core T (hamp ρ.P.ample) (hK ρ.P.ktriv) hsym hS S.N _
    hN hunit (hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _))
  obtain ⟨law, hmain⟩ := GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure hL ex.core T _ htest hind hch htors hfew
  let _ := law.grp
  let _ := law.comm
  obtain ⟨hsplit, hsemi, PP, cub, m, hF, he, hpull, hsym', hloc, -⟩ := hmain
  have hiso : LBIso T.L.L (PP.L.pull ex.core.a) := by
    obtain ⟨w, hw, -⟩ := hpull
    rw [← hF]
    exact ⟨w, hw⟩
  have e₁ := PolBaseChange.eSec_comm gp
  have e₂ := PolBaseChange.eSec_comm law.pull
  have hs : eSec ex.core.A ≫ ex.core.A.hom = 𝟙 _ := Over.w η[ex.core.A]
  have hsP : eSec ρ.P.A ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  have hsG : eSec ex.core.GG ≫ ex.core.GG.hom = 𝟙 _ := Over.w η[ex.core.GG]
  obtain ⟨w, hw, hv⟩ := exists_rescale ex.core.A.hom (eSec ex.core.A) hs _ _ _ e₁ _ _ _ e₂ ρ.P.isLB PP.isLB ρ.rig
    ρ.rig_gen PP.rig PP.rigGen (LBIso.trans (pull_isLB PP.isLB _) T.L.isLB (pull_isLB ρ.P.isLB _) hiso.symm hT)
  have hqc : QuasiCompact (Q.G.ι ≫ Q.P.hom) := (GlobalTheory.ZJ.core_basic ex.core).2.2.1
  have hpr := Q.proper
  have hqc' : QuasiCompact Q.G.ι := QuasiCompact.of_comp _ Q.P.hom
  refine ⟨{ u₀ := Q.u₀
            u₀_gen := Q.u₀_pt
            G := ex.core.GG
            grp := law.grp
            comm := law.comm
            semi := hsemi
            dim := law.smooth
            qproj := by
              have h := isQProjOver_ι Q.proj Q.G
              rw [← Category.assoc] at h
              exact h
            φ := ex.a
            cart := law.pull
            L := PP
            cub := cub
            sym := hsym' hsym
            w := w
            w_gen := hw
            w_rig := ?_
            split := hsplit }, ⟨Iso.refl _, Category.id_comp _, rfl, heq_of_eq (Category.comp_id _)⟩, hloc, ⟨law⟩⟩
  intro K _ g x y jP jL hx hy hP hL'
  let r : Sp K ⟶ U₀.toScheme := g ≫ pullback.snd ρ.P.A.hom Q.u₀
  have ry : r ≫ Q.u₀ = y := by
    have h := congrArg (· ≫ ρ.P.A.hom) hy
    simp only [Category.assoc] at h
    rw [pullback.condition] at h
    exact (Category.assoc _ _ _).trans (h.trans ((congrArg (y ≫ ·) hsP).trans (Category.comp_id _)))
  have rx : r ≫ U₀.ι = x := by
    have h := congrArg (· ≫ ex.core.GG.hom) hx
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) law.pull.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·) hsG).trans (Category.comp_id _))))))
  have rg : r ≫ eSec ex.core.A = g := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eSec ρ.P.A) ry).trans hy.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.comp_id _))
  let z : Sp K := IsLocalRing.closedPoint K
  have mP : pullback.fst ρ.P.A.hom Q.u₀ (g z) ∈ ρ.P.L.U jP := hP ⟨z, rfl⟩
  have mL : ex.a (g z) ∈ PP.L.U jL := hL' ⟨z, rfl⟩
  have key := hv _ r z jP jL ((congrArg (fun k => pullback.fst ρ.P.A.hom Q.u₀ (k z) ∈ ρ.P.L.U jP) rg).mpr mP)
    ((congrArg (fun k => ex.a (k z) ∈ PP.L.U jL) rg).mpr mL)
  erw [ry, rx, rg] at key
  exact valF_eq_mul_of_gm z (mem_pull.2 ((congrArg (fun k => k z ∈ ρ.P.L.U jP) hy).mp mP))
    (show g z ∈ (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)).U (fun _ => jP) ⊓ (PP.L.pull ex.a).U (fun _ => jL) from
      ⟨mem_pull.2 mP, mem_pull.2 mL⟩) (mem_pull.2 ((congrArg (fun k => k z ∈ PP.L.U jL) hx).mp mL)) key

end GlobalTheory.ClosureGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosureStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_groupScheme_cubical_bundle_closure : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  first | exact @GlobalTheory.ClosureGroup.exists_pre | exact GlobalTheory.ClosureGroup.exists_pre | (intros; apply GlobalTheory.ClosureGroup.exists_pre <;> assumption)
end
end

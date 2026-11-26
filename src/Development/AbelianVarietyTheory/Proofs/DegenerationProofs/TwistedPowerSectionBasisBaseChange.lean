module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.JetGlue
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.BasisBaseChange

open GlobalTheory.FieldBaseChange

section Algebra

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem basis_map_of_basis {φ : R →+* R'} (f : M →ₛₗ[φ] M') {I J : Type} [Fintype I] [Fintype J]
    (b : J → M) (β : I → M) (hb : ∀ s, ∃! a : J → R, s = ∑ j, a j • b j)
    (hβ : ∀ s, ∃! a : I → R, s = ∑ i, a i • β i)
    (hf : ∀ s, ∃! a : J → R', s = ∑ j, a j • f (b j)) (s : M') : ∃! a : I → R', s = ∑ i, a i • f (β i) := by
  classical
  choose u hu _ using fun i => hb (β i)
  choose w hw _ using fun j => hβ (b j)
  have huw : ∀ i i', ∑ j, u i j * w j i' = if i = i' then 1 else 0 := fun i => by
    have h1 : β i = ∑ i', (∑ j, u i j * w j i') • β i' := by
      conv_lhs => rw [hu i]
      simp only [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.smul_sum, ← hw j]
    have h2 : β i = ∑ i', (if i = i' then (1 : R) else 0) • β i' := by simp
    exact congrFun ((hβ (β i)).unique h1 h2)
  have fβ : ∀ a : I → R', ∑ i, a i • f (β i) = ∑ j, (∑ i, a i * φ (u i j)) • f (b j) := fun a => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hu i, map_sum]
    simp only [map_smulₛₗ, ← hu i]
  have fb : ∀ c : J → R', ∑ j, c j • f (b j) = ∑ i, (∑ j, c j * φ (w j i)) • f (β i) := fun c => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hw j, map_sum]
    simp only [map_smulₛₗ, ← hw j]
  have back : ∀ (a : I → R') i', ∑ j, (∑ i, a i * φ (u i j)) * φ (w j i') = a i' := fun a i' => by
    simp only [Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.mul_sum, ← map_sum, huw]
    simp [apply_ite φ]
  obtain ⟨c, hc, hcu⟩ := hf s
  refine ⟨_, hc.trans (fb c), fun a ha => funext fun i => ?_⟩
  rw [← hcu _ (ha.trans (fβ a)), back]

end Algebra

theorem isLin_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) {H : LB Y} {I : Type} [Fintype I]
    (s : I → SecOver p H) (a : I → R) (t : SecOver p H) : IsLin p s a t ↔ t = ∑ i, a i • s i := by
  have e : ∀ l, chartFun p H l (∑ i, a i • s i) = ∑ i, a i • chartFun p H l (s i) := fun l =>
    (map_sum (chartLin p H l) _ _).trans rfl
  exact ⟨fun h => SecOver.ext _ _ fun l => (h l).trans (e l).symm, fun h l => (congrArg (chartFun p H l) h).trans (e l)⟩

theorem basis_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {A : Over (Sp R)}
    {L : LB A.left} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (A.left ⟶ A.left)) (ε : K → ℤ) {m : ℕ}
    (b : Fin m → SecOver A.hom (LB.LinComb L ψ ε))
    (hb : IsSecBasis (T := Over.mk (spMap φ)) (A := A) _
      (fun i => DVR.pullSec L ψ ε (b i) (snd (Over.mk (spMap φ)) A).left))
    {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ A.left} (H : IsPullback π pB A.hom (spMap φ))
    {ψ' : K → (B ⟶ A.left)} (hψ : ∀ k, ψ' k = π ≫ ψ k) (s : SecOver pB (LB.LinComb L ψ' ε)) :
    ∃! a : Fin m → R', s = ∑ i, a i • pullOver L ε H.w hψ (b i) := by
  let T : Over (Sp R) := Over.mk (spMap φ)
  let p : (T ⊗ A).left ⟶ Sp R' := (fst T A).left
  let q : (T ⊗ A).left ⟶ A.left := (snd T A).left
  have H' : IsPullback q p A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) A.hom).flip
  let e := H.isoIsPullback _ _ H'
  have e1 : e.hom ≫ q = π := H.isoIsPullback_hom_fst _ _ H'
  have e2 : e.hom ≫ p = pB ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_hom_snd _ _ H'
  have e3 : e.inv ≫ π = q := H.isoIsPullback_inv_fst _ _ H'
  have e4 : e.inv ≫ pB = p ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_inv_snd _ _ H'
  have f1 : ∀ k, ψ' k = e.hom ≫ (q ≫ ψ k) := fun k => by rw [hψ, ← e1, Category.assoc]
  have f2 : ∀ k, q ≫ ψ k = e.inv ≫ ψ' k := fun k => by rw [hψ, ← e3, Category.assoc]
  let F := pullOver L ε e2 (φ := fun k => q ≫ ψ k) f1
  let G := pullOver L ε e4 (φ' := fun k => q ≫ ψ k) f2
  let b' : Fin m → SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε) := fun i => DVR.pullSec L ψ ε (b i) q
  have FG : ∀ t, F (G t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver e4 f2 _ _ hJ, Category.assoc, e.hom_inv_id, Category.comp_id]
  have GF : ∀ t, G (F t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e4 f2 _ _ hJ, sval_pullOver e2 f1 _ _ hJ, Category.assoc, e.inv_hom_id, Category.comp_id]
  have Fb : ∀ i, F (b' i) = pullOver L ε H.w hψ (b i) := fun i => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver H.w hψ _ _ hJ]
    exact (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.assoc, e1])
  have hb' : ∀ t : SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε), ∃! a : Fin m → R', t = ∑ i, a i • b' i := by
    intro t
    obtain ⟨r, hr, hu⟩ := hb t
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i), (isLin_iff p _ _ _).1 fun j => ?_,
      fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [constFn, e]
      rfl
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a i)) ((isLin_iff p _ _ _).2 ha)
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R')) (a i)).symm
  have Fs : ∀ a : Fin m → R', F (∑ i, a i • b' i) = ∑ i, a i • pullOver L ε H.w hψ (b i) := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, Fb, RingHom.id_apply]
  obtain ⟨a, ha, hu⟩ := hb' (G s)
  refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
  · show s = _
    rw [← Fs, ← ha, FG]
  · show G s = _
    rw [ha', ← Fs, GF]

theorem basis_pullback : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  intro hT R _ _ _ _ D N hN α R' _ φ B pB π H I _ β hβ s
  have hL := D.P.isLB
  obtain ⟨m, b, -, hb⟩ := hT R D N hN α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id R)) := by
    have : spMap (RingHom.id R) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := basis_of_isPullback (RingHom.id R) hL (D.famφB α) (DegPre.famε N) b
    (hb R (RingHom.id R) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε N) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have hψ : ∀ k, (fun i => π ≫ D.famφB α i) k = π ≫ D.famφB α k := fun _ => rfl
  have h1 := basis_of_isPullback φ hL (D.famφB α) (DegPre.famε N) b (hb R' φ _ fun _ _ => rfl) H hψ
  have h2 := basis_map_of_basis (pullOver D.P.L (DegPre.famε N) H.w hψ) b β h0
    (fun t => (existsUnique_congr fun a => isLin_iff D.P.A.hom β a t).1 (hβ t)) h1 s
  have e1 : ∀ i, pullOver D.P.L (DegPre.famε N) H.w hψ (β i) =
      DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H.w hψ _ _ hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm
  simp only [e1] at h2
  exact (existsUnique_congr fun a => isLin_iff pB _ a s).2 h2

end GlobalTheory.ZH.BasisBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPower_sectionBasis_baseChange : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  first | exact @GlobalTheory.ZH.BasisBaseChange.basis_pullback | exact GlobalTheory.ZH.BasisBaseChange.basis_pullback | (intros; apply GlobalTheory.ZH.BasisBaseChange.basis_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdIso

variable {X : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem mem_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  erw [Scheme.basicOpen_res]
  rfl

theorem isUnit_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (hV : V ≤ X.basicOpen a) :
    IsUnit (resG X h a) := by
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (resG X hV)
  rwa [rr] at this

theorem cancel {V : X.Opens} {J : Type} (a : J → Γ(X, V)) (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j))
    {u u' : Γ(X, V)} (h : ∀ j, u * a j = u' * a j) : u = u' := by
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  obtain ⟨j, hj⟩ := ha x hx
  have hu := (Scheme.mem_basicOpen X (a j) x hx).1 hj
  have := congrArg (X.presheaf.germ V x hx).hom (h j)
  rw [map_mul, map_mul] at this
  exact hu.mul_right_cancel this

theorem exists_unit {V : X.Opens} {J : Type} (a b : J → Γ(X, V))
    (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j)) (hb : ∀ j, X.basicOpen (a j) ≤ X.basicOpen (b j))
    (hab : ∀ j k, b j * a k = b k * a j) : ∃ w : Γ(X, V)ˣ, ∀ j, b j = w.val * a j := by
  have hu : ∀ j, IsUnit (resG X (X.basicOpen_le (a j)) (a j)) := fun j => isUnit_res _ _ le_rfl
  have hq : ∀ j, ∃ q : Γ(X, X.basicOpen (a j)), resG X (X.basicOpen_le (a j)) (b j) =
      q * resG X (X.basicOpen_le (a j)) (a j) := fun j =>
    ⟨resG X (X.basicOpen_le (a j)) (b j) * ↑(hu j).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : V ≤ ⨆ j, X.basicOpen (a j) := fun x hx => TopologicalSpace.Opens.mem_iSup.2 (ha x hx)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j => X.basicOpen (a j)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q j)
    have hV : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ V := inf_le_left.trans (X.basicOpen_le _)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq j)
    have e3 := congrArg (resG X hV) (hab i j)
    rw [map_mul, rr, rr] at e1 e2
    rw [map_mul, map_mul, e1, e2] at e3
    have u := (isUnit_res hV (a i) inf_le_left).mul (isUnit_res hV (a j) inf_le_right)
    apply u.mul_right_cancel
    linear_combination e3
  obtain ⟨r, hr'⟩ : ∃ r : Γ(X, V), ∀ j, resG X (X.basicOpen_le (a j)) r = q j :=
    (X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov q hcomp).exists
  have key : ∀ j, b j = r * a j := by
    intro j
    refine X.sheaf.eq_of_locally_eq' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov _ _ fun k => ?_
    change resG X (X.basicOpen_le (a k)) _ = resG X (X.basicOpen_le (a k)) _
    apply (hu k).mul_right_cancel
    rw [← map_mul, hab j k, map_mul, map_mul, hr', hq k]
    ring
  have hunit : IsUnit r := by
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_
    obtain ⟨j, hj⟩ := ha x hx
    have := hb j hj
    rw [key j, Scheme.basicOpen_mul] at this
    exact (Scheme.mem_basicOpen X r x hx).1 this.1
  exact ⟨hunit.unit, key⟩

theorem exists_pt (x : X) :
    ∃ (K : Type) (_ : Field K) (p : Sp K ⟶ X), ∀ U : X.Opens, ⊤ ≤ p ⁻¹ᵁ U ↔ x ∈ U := by
  refine ⟨X.residueField x, inferInstance, X.fromSpecResidueField x, fun U => ?_⟩
  have e := Scheme.fromSpecResidueField_apply x
  constructor
  · intro hU
    have := hU (Set.mem_univ (IsLocalRing.closedPoint (X.residueField x)))
    exact e _ ▸ this
  · intro hx y _
    exact (congrArg (· ∈ U) (e y)).mpr hx

theorem mem_chart {H : LB X} (t : H.Sec) (l : H.ι) {x : X} (hx : x ∈ nonzeroLocus t) (hl : x ∈ H.U l) :
    x ∈ X.basicOpen (t.f l) := by
  have hu := SecRatio.isUnit_res t l (V := nonzeroLocus t ⊓ H.U l) inf_le_left inf_le_right
  have : x ∈ X.basicOpen (resG X (inf_le_right : nonzeroLocus t ⊓ H.U l ≤ _) (t.f l)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ⟨hx, hl⟩
  exact ((mem_res _ _ _).1 this).2

variable {H H' : LB X} {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem val_prop (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    {K : Type} [Field K] (x : Sp K ⟶ X) (i : H.ι) (i' : H'.ι) (hi : ⊤ ≤ x ⁻¹ᵁ H.U i)
    (hi' : ⊤ ≤ x ⁻¹ᵁ H'.U i') :
    ∃ c : Kˣ, ∀ j, valR x _ ((s' j).f i') = c * valR x _ ((s j).f i) := by
  have h1 : Crd H s x (fun j => valR x _ ((s j).f i)) := ⟨i, 1, hi, fun j => by simp⟩
  have h2 : Crd H' s' x (fun j => valR x _ ((s' j).f i')) := ⟨i', 1, hi', fun j => by simp⟩
  exact CrdCalc.crd_unique (h K x _ h1) h2

theorem exists_chart_unit [IsReduced X] (hs : ⨆ j, nonzeroLocus (s j) = ⊤)
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    (i : H.ι) (i' : H'.ι) : ∃ w : Γ(X, H'.U i' ⊓ H.U i)ˣ, ∀ j,
      resG X inf_le_left ((s' j).f i') = w.val * resG X inf_le_right ((s j).f i) := by
  have hv : ∀ x ∈ H'.U i' ⊓ H.U i, ∃ (K : Type) (_ : Field K) (φ : Γ(X, H'.U i' ⊓ H.U i) →+* K) (c : Kˣ),
      (∀ j, φ (resG X inf_le_left ((s' j).f i')) = c * φ (resG X inf_le_right ((s j).f i))) ∧
      ∀ f, IsUnit (φ f) ↔ x ∈ X.basicOpen f := by
    intro x hx
    obtain ⟨K, _, p, hp⟩ := exists_pt x
    obtain ⟨c, hc⟩ := val_prop h p i i' ((hp _).2 hx.2) ((hp _).2 hx.1)
    refine ⟨K, inferInstance, CrdCalc.valHom p _ ((hp _).2 hx), c, fun j => ?_, fun f => ?_⟩
    · rw [← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ ((hp _).2 hx),
        CrdCalc.valR_res _ _ ((hp _).2 hx), hc]
    · rw [← CrdCalc.valR_eq, CrdCalc.isUnit_valR_iff _ _ ((hp _).2 hx), hp]
  apply exists_unit
  · intro x hx
    have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj hx.2⟩⟩
  · intro j x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    rw [← hunit, hc, Units.isUnit_units_mul, hunit]
    exact hx
  · intro j k
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    have := (hunit _).2 hx
    rw [map_sub, map_mul, map_mul, hc, hc] at this
    exact (this.ne_zero (by ring)).elim

theorem exists_iso_of_crd : ∀ (X : Scheme.{0}) [IsIntegral X] (H H' : LB X) (J : Type) (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → (∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v) → ∃ w : LB.Iso H H', w.IsGen ∧ ∀ j (x : X) (i : H.ι) (i' : H'.ι), x ∈ H.U i → x ∈ H'.U i' → gs (𝟙 X) x _ ((s' j).f i') = gs (𝟙 X) x _ (w.s (i', i)).val * gs (𝟙 X) x _ ((s j).f i) := by
  intro X _ H H' J s s' _ _ hs h
  choose w hw using exists_chart_unit hs h
  refine ⟨⟨fun p => w p.2 p.1⟩, ?_, ?_⟩
  · rintro ⟨i', i⟩ ⟨k', k⟩
    apply Units.ext
    have hi' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U i' := inf_le_left.trans inf_le_left
    have hi : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U i := inf_le_left.trans inf_le_right
    have hk' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U k' := inf_le_right.trans inf_le_left
    have hk : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U k := inf_le_right.trans inf_le_right
    refine cancel (V := H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k)) (fun j => resG X hi ((s j).f i)) ?_ fun j => ?_
    · intro x hx
      have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
      exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj (hi hx)⟩⟩
    · have e1 := congrArg (resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw i i' j)
      have e2 := congrArg (resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw k k' j)
      rw [map_mul, rr, rr] at e1 e2
      have e3 := SecRatio.compat_res (s j) i k hi hk
      have e4 := SecRatio.compat_res (s' j) i' k' hi' hk'
      have e5 : ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (le_inf hi hk) (H.g i k).val = 1 :=
        Units.inv_mul _
      change resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w i i').val *
          resG X hi ((s j).f i) =
        resG X (le_inf hi' hk') (H'.g i' k').val * ((res (le_inf hi hk) (H.g i k))⁻¹).val *
          resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hi ((s j).f i)
      rw [← e1, e4, e2, e3]
      linear_combination (-(resG X (le_inf hi' hk') (H'.g i' k').val *
        resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val *
        resG X hk ((s j).f k))) * e5
  · intro j x i i' hi hi'
    have hx : (𝟙 X : X ⟶ X) x ∈ H'.U i' ⊓ H.U i := ⟨hi', hi⟩
    have e := congrArg (gs (𝟙 X) x (H'.U i' ⊓ H.U i)) (hw i i' j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e
    exact e

end GlobalTheory.ZH.CrdIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ToImm
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep

theorem ext_local {T X : Scheme.{0}} (f g : T ⟶ X)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ T), y ≫ f = y ≫ g) : f = g :=
  ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t =>
    @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)

theorem exists_hom_of_ringHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (φ : Γ(X, U) →+* Γ(Y, V)) : ∃ g : V.toScheme ⟶ X, ∀ (R : Type) [CommRing R] (y : Sp R ⟶ V.toScheme)
      (h : ⊤ ≤ (y ≫ V.ι) ⁻¹ᵁ V), ∃ h' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U,
        ∀ f, valHom (y ≫ g) U h' f = valHom (y ≫ V.ι) V h (φ f) := by
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))
  refine ⟨h', fun f => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec
      U ⊤ ⊤ h0 le_rfl).symm
  have h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  have h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  unfold valHom
  rw [h4]
  rfl

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

theorem eq_zero_of_dense {Y : Scheme.{0}} [IsReduced Y] {K : Type} [Field K] {A : Type}
    (x : A → (Sp K ⟶ Y)) (hd : Dense (⋃ a, Set.range (x a))) (V : Y.Opens) (f : Γ(Y, V))
    (hf : ∀ a (h : ⊤ ≤ x a ⁻¹ᵁ V), valHom (x a) V h f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw, hw'⟩ := hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hw'
  have h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f := fun t' _ => by
    have : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hw
  have h2 : ⊤ ≤ x a ⁻¹ᵁ V := h1.trans ((x a).preimage_mono (Y.basicOpen_le f))
  have := (isUnit_valR_iff (x a) V h2 f).2 h1
  rw [valR_eq _ _ h2, hf a h2] at this
  exact (not_isUnit_zero this).elim

theorem comp_eq_of_const {k R : Type} [CommRing k] [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    (p' : Y ⟶ Sp k) (x : Sp R ⟶ X) (y : Sp R ⟶ Y) {U : X.Opens} {V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ V) (e : ∀ a, valHom x U h (constFn p U a) = valHom y V h' (constFn p' V a)) :
    x ≫ p = y ≫ p' := by
  refine eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)
  obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f
  have := e a
  rw [valHom_constFn, valHom_constFn] at this
  exact this

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {H : LB X} {H' : LB Y}
  {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem exists_chart [IsReduced Y] (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ)
    {K : Type} [Field K] {A : Type} (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X))
    (hd : Dense (⋃ a, Set.range (x a)))
    (hx : ∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) (i : J) :
    ∃ g : (nonzeroLocus (s' i)).toScheme ⟶ X, ∀ (R : Type) [CommRing R] [IsLocalRing R]
      (y : Sp R ⟶ (nonzeroLocus (s' i)).toScheme),
      (y ≫ g) ≫ p = (y ≫ (nonzeroLocus (s' i)).ι) ≫ p' ∧
        ∀ v, Crd H' s' (y ≫ (nonzeroLocus (s' i)).ι) v → Crd H s (y ≫ g) v := by
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i (Set.mem_univ i)
  choose r' hr' using fun j =>
    (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists
  let ev := MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r
  let ev' := MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'
  have hs : Function.Surjective ev := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hk : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro f hf
    refine eq_zero_of_dense x hd _ _ fun a h => ?_
    obtain ⟨e, v, hv', hv⟩ := hx a
    have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
    have h' := (crd_isUnit_iff i hv).1 hu
    have : (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply,
          valHom_constFn, e]
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        have e := (crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')
        rw [valR_eq _ _ h, valR_eq _ _ h'] at e
        exact hu.mul_right_cancel e
    have := congrArg (fun q => q f) this
    simp only [RingHom.comp_apply] at this
    rw [this, (RingHom.mem_ker).1 hf, map_zero]
  let φ := RingHom.liftOfSurjective ev hs ⟨ev', hk⟩
  have hφ : ∀ f, φ (ev f) = ev' f := fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f
  have hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a := fun a => by
    have := hφ (MvPolynomial.C a)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply] using this
  have hφr : ∀ j, φ (r j) = r' j := fun j => by
    have := hφ (MvPolynomial.X j)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_X'] using this
  obtain ⟨g, hg⟩ := exists_hom_of_ringHom hA _ φ
  refine ⟨g, fun R _ _ y => ?_⟩
  have h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i) := fun z _ => (y z).2
  obtain ⟨h', hv⟩ := hg R y h
  refine ⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩
  obtain ⟨w, hw⟩ := crd_exists hH s (y ≫ g)
  have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
  have hu' : IsUnit (w i) := (crd_isUnit_iff i hw).2 h'
  have := crd_smul (hu.unit * hu'.unit⁻¹) hw
  convert this using 2 with j
  rw [crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr,
    mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]

theorem exists_factor : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  intro k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx
  choose g hg using exists_chart hH hH' hI x x' hd hx
  let 𝒰 := Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc
  have hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i =
      pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j := by
    intro i j
    refine ext_local _ _ fun R _ _ y => ?_
    have e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι =
        (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨a₁, b₁⟩ := hg i R (y ≫ pullback.fst _ _)
    obtain ⟨a₂, b₂⟩ := hg j R (y ≫ pullback.snd _ _)
    obtain ⟨v, hv⟩ := crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)
    rw [← Category.assoc, ← Category.assoc]
    exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))
  have hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i :=
    fun i => 𝒰.ι_glueMorphisms g hcomp i
  have key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y),
      (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧
        ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v := by
    intro R _ _ y
    have : y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have h := (top_le_iff y _).2 hi
    have hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact h (Set.mem_univ z)
    have e := IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr
    have := hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)
    rwa [← hG i, ← Category.assoc, e] at this
  refine ⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_,
    fun R _ _ y => (key R y).2⟩
  · rw [← Category.assoc, (key R y).1]
  · obtain ⟨e, v, hv', hv⟩ := hx a
    exact eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv

end GlobalTheory.ZH.ToImm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_dense_points : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  first | exact @GlobalTheory.ZH.ToImm.exists_factor | exact GlobalTheory.ZH.ToImm.exists_factor | (intros; apply GlobalTheory.ZH.ToImm.exists_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsZpowMulIsUnitOfMem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc TopologicalSpace

section Points
variable {K C : Type} [Field K] [Field C] [IsAlgClosed C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} [LocallyOfFiniteType q]
  {σ : K →+* C}


variable (q σ) in
theorem exists_point_mem {Z : Set Y} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Sp C ⟶ Y, x ≫ q = spMap σ ∧ ∀ w, x w ∈ Z := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp C) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback q (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap σ))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z₀, rfl⟩ := (pullback.fst q (spMap σ)).surjective y
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := pullback.fst q (spMap σ) ⁻¹' Z) ⟨z₀, hy⟩
    (hZ.preimage (pullback.fst q (spMap σ)).continuous)
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (pullback.snd q (spMap σ)) z hz ≫ pullback.fst _ _,
    by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc], fun w => ?_⟩
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hzZ

theorem eq_of_val_eq [IsReduced Y] {W : Y.Opens} {r s : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r = valR x W s) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ (Y.basicOpen (r - s)).isOpen.isLocallyClosed ⟨y, hy⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => Y.basicOpen_le _ (hm w)
  have := ((isUnit_valR_iff x W hW (r - s)).2 fun w _ => hm w).ne_zero
  rw [valR_eq x W hW, map_sub, ← valR_eq, ← valR_eq, h x hx hW, sub_self] at this
  exact (this rfl).elim

theorem isUnit_of_val_ne_zero {W : Y.Opens} {r : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r ≠ 0) : IsUnit r := by
  refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 ?_
  by_contra hn
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ
    (W.isOpen.isLocallyClosed.inter (Y.basicOpen r).isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hn⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => (hm w).1
  obtain ⟨w⟩ : Nonempty ↥(Sp C) := inferInstance
  exact (hm w).2 ((isUnit_valR_iff x W hW r).1 (h x hx hW).isUnit (show w ∈ (⊤ : (Sp C).Opens) from trivial))

theorem exists_glue [IsReduced Y] {I : Type} (W : Y.Opens) (T : I → Y.Opens) (F : I → (Sp C ⟶ Y) → C)
    (hT : ∀ z, ∃ m, z ∈ T m) (hF : ∀ m, Reg q σ (W ⊓ T m) (F m))
    (h : ∀ m m' x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F m x = F m' x) :
    ∃ r : Γ(Y, W), ∀ m x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → F m x = valR x W r := by
  choose u hu using hF
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun m => W ⊓ T m) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.2 ((hT y).imp fun _ hm => ⟨hy, hm⟩)) u
    (fun m m' => eq_of_val_eq (q := q) (σ := σ) (W := W ⊓ T m ⊓ (W ⊓ T m')) fun x hx hW =>
      (valR_res x inf_le_left hW _).trans ((hu m x hx fun _ hz => (hW hz).1).symm.trans
        ((h m m' x hx (fun _ hz => (hW hz).1.1) (fun _ hz => (hW hz).1.2) fun _ hz => (hW hz).2.2).trans
          ((hu m' x hx fun _ hz => (hW hz).2).trans (valR_res x inf_le_right hW _).symm))))
  refine ⟨r, fun m x hx hW hm => ?_⟩
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ T m) := fun _ hz => ⟨hW hz, hm hz⟩
  rw [hu m x hx hh, ← hr m]
  exact valR_res x inf_le_left hh r

end Points


open GlobalTheory.PrimeSection in
theorem exists_zpow_mul_isUnit_of_mem {X : Scheme.{0}} {t : Γ(X, ⊤)} {ξ : X}
    (hη : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U → Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    [IsIntegral X] [IsLocallyNoetherian X] {A : Type} {U : A → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
    {a₀ : A} (h₀ : ξ ∈ U a₀) (hg : ∀ a b, IsUnit (g a b)) (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have hD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hx₀ : X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀) (r a₀) ≠ 0 := ((hru a₀).map _).ne_zero
  have hτn : ∀ n : ℤ, X.presheaf.germ _ _ hD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      algebraMap _ X.functionField (X.presheaf.germ ⊤ ξ trivial t) ^ n := fun n ↦ by
    rw [algebraMap_germ, ← germ_res (le_top : X.basicOpen t ≤ ⊤) hD, ← hτ]
    let φ : Γ(X, X.basicOpen t) →+* X.functionField := (X.presheaf.germ _ _ hD).hom
    change φ _ = φ _ ^ n
    rw [← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hn⟩, -⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hx₀
  have : ∀ a, ∃ s : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op s =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a :=
    fun a ↦ exists_res_eq hη hp _ fun h ↦
      ⟨X.presheaf.germ (U a ⊓ U a₀) ξ ⟨h, h₀⟩ (g a a₀) * u, by
        rw [map_mul, map_mul, hn, germ_res, hτn, algebraMap_germ,
          germ_eq_mul_germ hr (a := a) _ (genericPoint_mem_inf hp h₀)]
        ring⟩
  choose s hs using this
  have hs₀ : ξ ∈ X.basicOpen (s a₀) := by
    rw [X.mem_basicOpen _ ξ h₀]
    convert hu
    apply IsFractionRing.injective _ X.functionField
    have := congrArg (X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀)) (hs a₀)
    rw [map_mul, germ_res, germ_res, hτn] at this
    rw [algebraMap_germ, hn, this]
  refine ⟨n, s, fun b ↦ isUnit_of_isUnit_res hη hp ?_ fun h ↦
    mem_basicOpen_of_compatible hg (compatible_of_res_eq hD hr _ hs) h hs₀, hs⟩
  rw [hs b]
  exact ((Units.isUnit _).map _).mul (hru b)


open GlobalTheory.DvrModel GlobalTheory.PrimeSection in
theorem norm_const : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (A I : Type) (U : A → H.Opens) (T : I → HK.Opens) (F : A → I → (Sp (PadicAlgCl p) ⟶ HK) → PadicAlgCl p), (∀ z, ∃ m, z ∈ T m) → (∀ a m, Reg q σ (j ⁻¹ᵁ U a ⊓ T m) (F a m)) → (∀ a m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → F a m x ≠ 0) → (∀ a m m' x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F a m x = F a m' x) → (∀ a a', ∃ g : Γ(H, U a ⊓ U a')ˣ, ∀ m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a' → ⊤ ≤ x ⁻¹ᵁ T m → F a m x = valR (x ≫ j) (U a ⊓ U a') g.val * F a' m x) → ∃ κ : ℝ, 0 < κ ∧ ∀ a m (c : Sp (OO p) ⟶ H) x, c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ‖F a m x‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hsm hgi hK A I U T F hT hreg hne h₁ h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isOpenImmersion_generic hK
  have := GlobalTheory.DvrModel.isIntegral hK
  have := GlobalTheory.DvrModel.isLocallyNoetherian f
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hK inferInstance
  have hη := notMem_basicOpen_iff_specializes hϖ hs
  by_cases hA : ∃ a₀, pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) (genericPoint _) ∈ U a₀
  swap
  · refine ⟨1, one_pos, fun a m c x hc _ _ ha _ => (hA ⟨a, mem_of_notMem_basicOpen hη
      (ha (show IsLocalRing.closedPoint (OO p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)) ?_⟩).elim⟩
    rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, hc]
    exact IsLocalRing.comap_closedPoint jV
  obtain ⟨a₀, h₀⟩ := hA
  choose r hr using fun a => exists_glue (j ⁻¹ᵁ U a) T (F a) hT (hreg a) (h₁ a)
  choose g hg using h₂
  have hpt : ∀ x : Sp (PadicAlgCl p) ⟶ HK, ∃ m, ⊤ ≤ x ⁻¹ᵁ T m := fun x =>
    (hT _).imp fun m hm => (top_le_iff x _).2 hm
  have hru : ∀ a, IsUnit (r a) := fun a => isUnit_of_val_ne_zero (q := q) (σ := σ) fun x hx hW => by
    obtain ⟨m, hm⟩ := hpt x
    rw [← hr a m x hx hW hm]
    exact hne a m x hx hW hm
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨r', τ', hτ', hr', -, hu', E⟩ := exists_transport (opensRange_generic hϖ hK)
    (g := fun a b => (g a b).val) (fun a => rfl) r
    (fun a b => eq_of_val_eq (q := q) (σ := σ) fun x hx hW => by
      obtain ⟨m, hm⟩ := hpt x
      have ha : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := fun _ hz => (hW hz).1
      have hb : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U b := fun _ hz => (hW hz).2
      refine (valR_res x inf_le_left hW _).trans (((hr a m x hx ha hm).symm.trans (hg a b m x hx ha hb hm)).trans
        (Eq.symm ((valR_mul x _ hW _ _).trans (congrArg₂ (· * ·) (GlobalTheory.Points.valR_appLE x j _ hW _) ?_))))
      exact (valR_res x inf_le_right hW _).trans (hr b m x hx hb hm).symm)
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm
  obtain ⟨n, s, hsu, hs'⟩ := exists_zpow_mul_isUnit_of_mem hη (prime_res_generic hϖ hs) h₀
    (fun a b => (g a b).isUnit) τ' hτ' hr' fun a => hu' a (hru a)
  have hpos : 0 < ‖σ (algebraMap V K ϖ)‖ ^ n := zpow_pos (norm_pos_iff.2 ((map_ne_zero σ).2 h0)) n
  refine ⟨(‖σ (algebraMap V K ϖ)‖ ^ n)⁻¹, inv_pos.2 hpos, fun a m c x hc hx hq ha hm => ?_⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := by
    show ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a
    rw [hx]
    exact fun _ _ => ha trivial
  have e := congrArg (valR x _) ((E n a (s a)).1 (hs' a))
  have e₁ : valR x ⊤ (Units.map φ.toMonoidHom (Units.mk0 _ h0)).val = σ (algebraMap V K ϖ) :=
    (GlobalTheory.Points.valR_comp x q ⊤ _).symm.trans (by
      rw [hq]
      exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom σ) _)
  have e₂ : ((valR c (U a) (s a) : OO p) : PadicAlgCl p) = σ (algebraMap V K ϖ) ^ n * F a m x := by
    rw [hr a m x hq hW hm, ← e₁, ← val_zpow x (U := ⊤) (fun _ _ => trivial)]
    refine Eq.trans ?_ ((e.trans (valR_mul x _ hW _ _)).trans (congrArg (· * _) (valR_res x le_top hW _)))
    refine Eq.trans ?_ (GlobalTheory.Points.valR_appLE x j _ hW _).symm
    rw [hx]
    exact ((valR_spMap (OO p).subtype c _ ha).2 _).symm
  have e₃ : ‖((valR c (U a) (s a) : OO p) : PadicAlgCl p)‖ = 1 := by
    have hu : IsUnit (valR c (U a) (s a)) := by
      rw [valR_eq c _ ha]
      exact (hsu a).map _
    obtain ⟨d, hd⟩ := hu.exists_right_inv
    have e' := congrArg (fun z : OO p => ‖(z : PadicAlgCl p)‖) hd
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at e'
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  rw [e₂, norm_mul, norm_zpow] at e₃
  exact eq_inv_of_mul_eq_one_right e₃

end GlobalTheory.ZH.FrameNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsOfIsEE
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_of_isEE :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.HasTests → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hT hO hE
  have := hb.ft
  have := hb.char
  have h1 := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have h2 := exists_at_test_of_cen o Ω S M U₀ hT hO
  have h3 := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have h4 := isoFree_TT_and_supI_specializes o Ω S M U₀ hO h1 h2 h3
  have h5 := EE_contains_stable_weightZero o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  have h6 := coord_regular_and_unit o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  exact ⟨hO, hE, h1.2, fun z p _ y y₀ τ hc ha => (h3 z p y y₀ τ hc ha).2, h4.1, h4.2.2.1,
    fun ξ => (h5 ξ).1, fun ξ => (h5 ξ).2.1, fun ξ => (h5 ξ).2.2, h6⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem weilIs_uTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u x hx a b c hc
  have hpos : (S.r * S.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have hζ : IsUnit S.ζ := S.prim.isUnit hpos
  obtain ⟨c₀, hc₀⟩ := (hζ.pow (S.r * S.N * (eStd S.g _ a b).val)).map (algebraMap o S.R)
  have H := ρ.weil a b c₀ hc₀
  have hf : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    exact (Spec.map_comp (CommRingCat.ofHom u.yK)
      (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))).symm
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk (spMap y₀) ((Category.comp_id _).trans hf.symm)
  have H' := CommPairing.weilIs_pull hL.globalFns ρ.P.isAb ρ.P.isLB h H
  have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn c₀) = unitOn c := by
    refine Units.ext ?_
    refine (congrArg (fun q => q.hom c₀.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y₀))).symm.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom (y₀ c₀.val) =
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c.val
    rw [hc, hc₀]
  rw [e] at H'
  exact (weilIs_grpPullback_of_comm' _ _ ρ.P.A u.A.A (spMap u.yK) u.φ ρ.P.L u.A.L ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (x a) (x b) (h ≫ ρ.pt a) (h ≫ ρ.pt b) (unitOn c) (hx a).symm (hx b).symm).2 H'

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_labelledTorsion_uniformTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  first | exact @GlobalTheory.ZH.weilIs_uTest | exact GlobalTheory.ZH.weilIs_uTest | (intros; apply GlobalTheory.ZH.weilIs_uTest <;> assumption)
end
end

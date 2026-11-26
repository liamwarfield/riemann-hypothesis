module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefficientFieldOfCharZero
open IsLocalRing

namespace GlobalTheory.CohenRegular

section Field
open Polynomial

theorem exists_coefficientField_of_charZero (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Field

open MvPowerSeries GlobalTheory.CohenStructure

end GlobalTheory.CohenRegular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjectiveOfResidueOfCotangent
open IsLocalRing Matrix TensorProduct

namespace GlobalTheory.LocalSurj

theorem exists_sub_mem_map_pow_succ {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (n : ℕ) (a : A)
    (ha : a ∈ (m ^ n).map f) : ∃ x ∈ m ^ n, a - f x ∈ (m ^ (n + 1)).map f := by
  change a ∈ Ideal.span (f '' ((m ^ n : Ideal R) : Set R)) at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨x', hx2, hx2'⟩ := hz
    refine ⟨x + x', add_mem hx hx2, ?_⟩
    have : y + z - f (x + x') = (y - f x) + (z - f x') := by rw [map_add (f := _)]; ring
    rw [this]; exact add_mem hx' hx2'
  | smul c y _ hy =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨s, hs⟩ := hm c
    refine ⟨s * x, Ideal.mul_mem_left _ _ hx, ?_⟩
    have : c • y - f (s * x) = c * (y - f x) + (c - f s) * f x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_left _ _ hx') ?_
    rw [pow_succ', Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem f hx)

noncomputable def approx {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) :
    (n : ℕ) → {x : R // a - f x ∈ (m ^ n).map f}
  | 0 => ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | n + 1 =>
    let p := approx f m hm a n
    let h := exists_sub_mem_map_pow_succ f m hm n _ p.2
    ⟨p.1 + h.choose, by
      have := h.choose_spec.2
      rwa [map_add, ← sub_sub]⟩

theorem approx_succ_sub {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by
  simp only [approx, add_sub_cancel_left]
  exact (exists_sub_mem_map_pow_succ f m hm n _ (approx f m hm a n).2).choose_spec.1

theorem approx_sub_mem {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have e : (approx f m hm a (n + 1)).1 - (approx f m hm a k).1 =
        ((approx f m hm a (n + 1)).1 - (approx f m hm a n).1) +
        ((approx f m hm a n).1 - (approx f m hm a k).1) := by ring
    rw [e]
    exact add_mem (Ideal.pow_le_pow_right hkn (approx_succ_sub f m hm a n)) ih

theorem surjective_of_residue_of_cotangent (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : R →+* A)
    (hc : IsAdicComplete (maximalIdeal R) R) (hf : IsLocalHom f)
    (hres : ∀ z : A, ∃ r, z - f r ∈ maximalIdeal A)
    (hcot : maximalIdeal A ≤ (maximalIdeal R).map f ⊔ maximalIdeal A ^ 2) :
    Function.Surjective f := by
  set m := maximalIdeal R

  have hle : maximalIdeal A ≤ m.map f := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · simpa [pow_two, Ideal.smul_eq_mul] using hcot
  have hm : ∀ z : A, ∃ r, z - f r ∈ m.map f := fun z =>
    (hres z).imp fun r hr => hle hr
  have hmap : m.map f ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit f x hx
  intro a

  obtain ⟨L, hL⟩ := hc.prec' (fun n => (approx f m hm a n).1) (fun {k n} h => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact approx_sub_mem f m hm a h)
  refine ⟨L, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_iInf]
  intro n
  have h1 := (approx f m hm a n).2
  have h2 := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h2
  have e : a - f L = (a - f (approx f m hm a n).1) + f ((approx f m hm a n).1 - L) := by
    rw [map_sub]; ring
  rw [e]
  refine (Ideal.map_pow f m n ▸ Ideal.pow_right_mono hmap n) (add_mem h1 (Ideal.mem_map_of_mem f h2))

end GlobalTheory.LocalSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinates
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FamFrom

theorem rescale_inv_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (χ : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)).psi χ = D.psi χ := by
  show GlobalTheory.UU.scaleGen _ (GlobalTheory.UU.scaleGen _ _) = _
  unfold GlobalTheory.UU.scaleGen
  generalize D.psi χ = b
  cases b
  congr 1
  funext j
  have h1 : unitOn ((g χ)⁻¹) * unitOn (g χ) = 1 := by
    have hu : unitOn ((g χ)⁻¹ * g χ) = unitOn ((g χ)⁻¹) * unitOn (g χ) := map_mul _ _ _
    rw [← hu, inv_mul_cancel]
    exact Units.ext (map_one _)
  rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]

theorem isPullDeg_rescale_inv {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] (φ : W →+* R)
    (D₀ : DegPre W) (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (hD : IsPullDeg φ D₀ D) :
    ∃ h : IsPullDeg φ D₀ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)),
      (∀ y, h.xe y = hD.xe y) ∧ h.e.hom.left = hD.e.hom.left :=
  ⟨{ hD with psi_pr := fun x => (rescale_inv_psi D g x).symm ▸ hD.psi_pr x }, fun _ => rfl, rfl⟩

end GlobalTheory.UCanon.FamFrom

namespace GlobalTheory.UCanon.FamFrom

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  intro E _ _ _ H Dl l c L R _ _ _ hB iw hiw m N s ε hε hs hu hpos hdef hnt
  letI := H.starRing
  have hw : H.w0 + star H.w0 = 1 := GlobalTheory.TauTwist.halfUnit_add_star H
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  letI iD : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨he0, hb0, hU0, oa0, hoa0, hW0⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  have hne : ∃ i, ε (.inl i) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : L.D.X)
    have h := hdef y hy
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨i, fun h0 => hi (by rw [h0]; rfl)⟩
  obtain ⟨D'', hD, iM, e, hxe, hPE, hTB, hPI, hfin, ⟨oa1, hoa1, hPW⟩, hmono, -, -, -⟩ :=
    GlobalTheory.UTautData.main L.W R (maximalIdeal R) iw hiw (mulDeg L.D l.M') (𝓞 E) oa0 H.w0 hw he0 hb0 hW0 hU0
      (fun i => s (.inl i)) (fun i => (hs i).2) (fun i => (hs i).1) (fun j => (hu j).unit) l.M' hM
      (fun i => ε (.inl i)) (fun j => ε (.inr j)) (fun i => hε _) hpos (fun j => hε _) hdef hne

  set T := GlobalTheory.UTautData.taut D'' e H.w0 (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit) l.M'
    (fun i => ε (.inl i)) (fun j => ε (.inr j)) with hT
  let D1 : DegData R (maximalIdeal R) := ⟨T, hPE, hTB, hPI, hfin⟩
  obtain ⟨t, P, hPD, hmod, hoD⟩ := GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm H R hB D1 (inst := iM) oa1 hPW
  have key : ∀ (Dd : DegData R (maximalIdeal R)) [im : Module (𝓞 E) Dd.toPre.X] (od : Dd.toPre.OAct (𝓞 E)),
      Dd = D1 → HEq im iM → HEq od oa1 → ∃ e' : Dd.toPre.X ≃ₗ[𝓞 E] L.D.X,
        DivFrom L Dd.toPre od iw s ε e' ∧
        IsMonomial Dd.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e'.toLinearMap (ε (.inl i))) := by
    rintro Dd im od rfl h1 h2
    have h1' := eq_of_heq h1
    subst im
    have h2' := eq_of_heq h2
    subst od
    letI : Module (𝓞 E) D1.toPre.X := iM
    let e₁ : D1.toPre.X ≃ₗ[𝓞 E] L.D.X := e
    refine ⟨e₁, ?_, hmono⟩
    obtain ⟨h2p, hx2, he2⟩ := isPullDeg_rescale_inv iw (mulDeg L.D l.M') D''
      (GlobalTheory.UTautData.scaleFn (GlobalTheory.UTautData.coordsK (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit))
        H.w0 (GlobalTheory.UTautData.forms l.M' (fun i => pull e.toLinearMap (ε (.inl i)))
          (fun j => pull e.toLinearMap (ε (.inr j))))) hD
    refine ⟨_, h2p, fun y => ?_, fun y => (hx2 y).trans (hxe y).symm, fun x => ?_⟩
    · rw [inv_inv]
      refine (GlobalTheory.UTautData.scaleFn_coe _ _ _ _ _ _ _ _).trans ?_
      rw [Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inl i)) ^ ((l.M' : ℤ) * ε (.inl i) (e₁ y) (H.w0 • e₁ y))
        rw [← h3]
        rfl
      · refine Finset.prod_congr rfl fun j _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inr j)) ^ ((l.M' : ℤ) * ε (.inr j) (e₁ y) (H.w0 • e₁ y))
        rw [← h3, (hu j).unit_spec]
        rfl
    · rw [he2]
      have h := hoa1 x
      rw [hoa0] at h
      exact h
  obtain ⟨e', h1, h2⟩ := key P.D P.oD hPD hmod hoD
  exact ⟨t, P, e', h1, h2⟩

end GlobalTheory.UCanon.FamFrom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_family_from_regular_base_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  first | exact @GlobalTheory.UCanon.FamFrom.main | exact GlobalTheory.UCanon.FamFrom.main | (intros; apply GlobalTheory.UCanon.FamFrom.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricChartRingFactorisationLocalHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParameters
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem sum_residue_smul_toCotangent {R : Type} [CommRing R] [IsLocalRing R] {Idx : Type} [Fintype Idx]
    (a : Idx → R) (y : Idx → R) (hy : ∀ i, y i ∈ maximalIdeal R) :
    ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨y i, hy i⟩ =
      (maximalIdeal R).toCotangent ⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ := by
  have h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) =
      ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R) := by
    ext; simp [smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

end GlobalTheory.CohenChart

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem exists_ringEquiv_chartRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R),
    (∀ i, t i ∈ maximalIdeal R) →
    (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) →
    ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  intro R _ _ hc hQ m t ht hind
  classical
  obtain ⟨q⟩ := hQ
  letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra
  haveI : CharZero (ResidueField R) := algebraRat.charZero _
  haveI := hc
  obtain ⟨Λ, hF, hΛ⟩ := GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R
  letI := hF.toField

  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩
  have hv : LinearIndependent (ResidueField R) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (R := R) (g j)
    have h1 : ∑ j, residue R (a j) • v j = 0 := by simpa [ha] using hg
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero] at h1
    rw [← ha i, residue_eq_zero_iff]
    exact hind a h1 i
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hmd : m ≤ d := by simpa using hv.fintype_card_le_finrank
  set W := Submodule.span (ResidueField R) (Set.range v) with hW
  have hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = m := by rw [finrank_span_eq_card hv]; simp
    omega
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd
  choose w hw using fun j => W.mkQ_surjective (b j)
  choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)
  let x : Fin m ⊕ Fin (d - m) → R := Sum.elim t (fun j => (s j : R))
  have hx : ∀ j, x j ∈ maximalIdeal R := by
    rintro (j | j)
    exacts [ht j, (s j).2]
  let g : Fin m ⊕ Fin (d - m) → CotangentSpace R := fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩
  set U := Submodule.span (ResidueField R) (Set.range g) with hU
  have hUtop : ∀ y : CotangentSpace R, y ∈ U := by
    intro y
    have hWU : W ≤ U := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have hwU : ∀ j, w j ∈ U := fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩
    have h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]
    have h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    have h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U := U.sum_mem fun j _ => U.smul_mem _ (hwU j)
    have := U.add_mem (hWU h2) h3
    simpa using this

  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  let f : ChartRing Λ m (d - m) →ₐ[Λ] R := GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx
  have hfX : ∀ j, f (X j) = x j := fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j
  have hfC : ∀ a : Λ, f (C a) = a := fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a
  have hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R := by
    intro g hg
    have h4 := GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g
    have h5 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m)) := fun j =>
    GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  have hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R) := ⟨fun g hg => by
    by_contra hn
    exact (hle g hn) hg⟩
  have hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R := by
    intro z
    obtain ⟨a, ha, h⟩ := hΛ z
    exact ⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩
  have hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔
      maximalIdeal R ^ 2 := by
    intro z hz
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1
      (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))
    choose a ha using fun j => residue_surjective (R := R) (c j)
    have h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩ := by simpa [ha] using hc'
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq] at h1
    have h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) :=
      sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))
    have h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j) := by ring
    rw [h3]
    refine Submodule.add_mem_sup h2 ?_
    have : (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z) := by ring
    rw [this]
    exact neg_mem h1
  have hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m)) :=
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
      (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv
      (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))
  have hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot
  letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra
  haveI : Module.Finite (ChartRing Λ m (d - m)) R :=
    Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj
  have hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]
    have hmd' : m + (d - m) = d := by omega
    rw [hmd']
  have hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR
  let φ := RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩
  refine ⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  show t i = f (X (Sum.inl i))
  rw [hfX]
  rfl

end GlobalTheory.CohenChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParametersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R), (∀ i, t i ∈ maximalIdeal R) → (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) → ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  first | exact @GlobalTheory.CohenChart.exists_ringEquiv_chartRing | exact GlobalTheory.CohenChart.exists_ringEquiv_chartRing | (intros; apply GlobalTheory.CohenChart.exists_ringEquiv_chartRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricChartRingFactorisationLocalHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isComplAt_ringEquiv_comp {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (ψ : A →+* R) (σ : R ≃+* S) (h : IsComplAt ψ) : IsComplAt ((σ : R →+* S).comp ψ) := by
  obtain ⟨hN, hC, hF, hM, hR⟩ := h
  have hmap : (maximalIdeal R).map σ = maximalIdeal S := map_ringEquiv_maximalIdeal σ
  have hcomap : (maximalIdeal S).comap (σ : R →+* S) = maximalIdeal R := by
    rw [← hmap]; exact Ideal.comap_map_of_bijective _ σ.bijective
  refine ⟨isNoetherianRing_of_ringEquiv R σ, ?_, ?_, ?_, ?_⟩
  · haveI := hC
    rw [← hmap, IsAdicComplete.congr_ringEquiv]; exact hC
  · exact RingHom.Flat.comp hF (RingHom.Flat.of_bijective σ.bijective)
  · rw [← Ideal.comap_comap, hcomap, ← Ideal.map_map, hM]; exact hmap
  · intro s
    obtain ⟨a, b, hb, hab⟩ := hR (σ.symm s)
    refine ⟨a, b, ?_, ?_⟩
    · simpa using hb.map (σ : R →+* S)
    · have : (σ : R →+* S) (σ.symm s * ψ b - ψ a) ∈ maximalIdeal S := by
        rw [← Ideal.mem_comap, hcomap]; exact hab
      simpa using this

theorem exists_chartRing_factor : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  intro W _ _ hQ m N V _ _ hV ψV hCV hXV
  obtain ⟨R, _, _, _, ψ, θ, hψ, hθ, hθψ, hψC⟩ :=
    exists_complAt_factor_of_isAdicComplete W (Fin m ⊕ Fin N) V hV ψV hCV
  obtain ⟨hreg, -⟩ := isRegularLocalRing_and_isDomain_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC
  haveI := hreg
  let t : Fin m → R := fun i => ψ (MvPolynomial.X (.inl i))
  have ht : ∀ i, t i ∈ maximalIdeal R := by
    intro i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (θ (t i)) := hu.map θ
    have h2 : θ (t i) = ψV (MvPolynomial.X (.inl i)) := by
      show (θ.comp ψ) _ = _; rw [hθψ]
    rw [h2] at h1
    exact (mem_maximalIdeal _).1 (hXV i) h1
  have hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha i
    exact cotangent_indep_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC m (Function.Embedding.inl) ht a
      (Ideal.mem_sup_left ha) i
  have hQR : Nonempty (ℚ →+* R) := ⟨(ψ.comp MvPolynomial.C).comp hQ.some⟩
  obtain ⟨k, _, e, σ, hσ⟩ := GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters R hψ.2.1 hQR m t ht hind
  refine ⟨k, inferInstance, e, (σ : R →+* ChartRing k m e).comp ψ, θ.comp (σ.symm : ChartRing k m e →+* R),
    isComplAt_ringEquiv_comp ψ σ hψ, inferInstance, ?_, ?_, ?_⟩
  · rw [← hθψ]; ext x <;> simp
  · show IsLocalHom ((σ : R →+* ChartRing k m e).comp (ψ.comp MvPolynomial.C))
    infer_instance
  · intro i; exact hσ i

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricChartRingFactorisationLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricChartRing_factorisation_localHom : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  first | exact @GlobalTheory.TChart.exists_chartRing_factor | exact GlobalTheory.TChart.exists_chartRing_factor | (intros; apply GlobalTheory.TChart.exists_chartRing_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem injective_of_flat_of_isDomain {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R] (ψ : A →+* R)
    (h : ψ.Flat) : Function.Injective ψ := by
  letI := ψ.toAlgebra
  haveI : Module.Flat A R := h
  refine (injective_iff_map_eq_zero ψ).2 fun a ha => ?_
  by_contra h0
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : a • (1 : R) = a • (0 : R) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, _root_.mul_one]; exact ha
  exact one_ne_zero (hr h1)

theorem exists_canon_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hn
  obtain ⟨D', L, θ₀, N, ε, e, s, hp, hq, hθ₀, hb, hδ, hs, hu, hdiv⟩ := GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue Xo c φ V hV hk C hn
  have hC₀ : (MvPolynomial.eval₂Hom θ₀ s).comp MvPolynomial.C = θ₀ := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ _
  have hsm : ∀ i, s (.inl i) ∈ maximalIdeal V := fun i => by
    obtain ⟨u, hu⟩ := (hs i).symm
    rw [← hu]; exact Ideal.mul_mem_right _ _ (C.s_mem i)
  have hs0 : ∀ i, s (.inl i) ≠ 0 := fun i h => C.s_ne_zero i ((hs i).eq_zero_iff.1 h)
  obtain ⟨k, _, e', ψ, θ, hcompl, hθ, hθψ, hψ, hbd⟩ := GlobalTheory.T.exists_toricChartRing_factorisation_localHom L.W ⟨L.b.comp (algebraMap ℚ c.F)⟩ C.m N V hV.1.2.2.2
    (MvPolynomial.eval₂Hom θ₀ s) (by rw [hC₀]; exact hθ₀) (fun i => by rw [MvPolynomial.eval₂Hom_X']; exact hsm i)
  have hθX : ∀ j, θ (ψ (MvPolynomial.X j)) = s j := fun j => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = θ₀ := by rw [← RingHom.comp_assoc, hθψ, hC₀]
  have hinj : Function.Injective (ψ.comp MvPolynomial.C) :=
    (injective_of_flat_of_isDomain ψ hcompl.2.2.1).comp (MvPolynomial.C_injective _ _)
  let b₁ : c.F →+* ChartRing k C.m e' := (ψ.comp MvPolynomial.C).comp L.b
  have hR : GlobalTheory.Mum.Base (ChartRing k C.m e') :=
    ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k C.m e', (b₁.charZero_iff b₁.injective).1 inferInstance⟩
  have htor : ∀ j, IsUnit (ψ (MvPolynomial.X (.inr j))) := fun j => hθ.map_nonunit _ (by rw [hθX]; exact hu j)
  have hmem : ∀ i, ψ (MvPolynomial.X (.inl i)) ∈ maximalIdeal (ChartRing k C.m e') := fun i hi =>
    hsm i (by rw [← hθX]; exact hi.map θ)
  have hne : ∀ i, θ (ψ (MvPolynomial.X (.inl i))) ≠ 0 := fun i => by rw [hθX]; exact hs0 i
  have hval : ∀ i y, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y = C.δ i (e.symm y) (e.symm y) := fun i y => by
    rw [hδ i]
    show _ = (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm y)) (e (e.symm y))
    rw [e.apply_symm_apply]
  have hnn : ∀ i y, 0 ≤ (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun i y => by
    rw [hval]; exact C.cone.nonneg i _
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun y hy => by
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (y := e.symm y) (by simpa using hy)
    refine Finset.sum_pos' (fun j _ => hnn j y) ⟨i, Finset.mem_univ _, ?_⟩
    rw [hval]
    exact pos_of_mul_pos_left (by rw [mul_comm]; exact hi) (Int.natCast_nonneg l.M')
  obtain ⟨t₁, P₁, e₁, hdiv₁, hmono⟩ := GlobalTheory.T.mumford_family_from_regular_base_coordinates L (ChartRing k C.m e') hR (ψ.comp MvPolynomial.C) hinj C.m N
    (fun j => ψ (MvPolynomial.X j)) (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) (fun j => (ε j).2)
    (fun i => ⟨hmem i, fun h => hne i (by rw [h, map_zero])⟩) htor hnn hpos e.injective.nontrivial
  obtain ⟨y₁, yo, κ, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.classified_on_open_of_specialises_to_classified Xo c φ D' L (ChartRing k C.m e') V hR hV C.toFam t₁ P₁
    (ψ.comp MvPolynomial.C) θ hθ (by rw [← RingHom.comp_assoc, hθC, hb]) C.m N (fun j => ψ (MvPolynomial.X j))
    (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) e₁ e (fun j => (ε j).2) hne htor hdiv₁
    (by rw [hθC, funext hθX]; exact hdiv)
  have hrk : Module.finrank (𝓞 E) P₁.D.toPre.X = Module.finrank (𝓞 E) C.P.D.toPre.X := (e₁.trans e.symm).finrank_eq
  have hcone : IsCone H.bar φ fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
    have h := C.cone.pull_equiv (e₁.trans e.symm)
    have he : (fun i => pull (e₁.trans e.symm).toLinearMap (C.δ i)) =
        fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
      funext i
      rw [hδ i]
      refine LinearMap.ext₂ fun a b => ?_
      show (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm (e₁ a))) (e (e.symm (e₁ b))) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    rwa [he] at h
  let C₁ : MonoFam Xo c φ (ChartRing k C.m e') :=
    ⟨⟨b₁, t₁, P₁, y₁, h₁, h₂⟩, C.m, fun i => ψ (MvPolynomial.X (.inl i)), hmem,
      fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X), hcone, hrk.le.trans C.rank, hmono⟩
  exact ⟨k, _, C.m, e', C₁, θ, ⟨⟨D', by rw [← hp, ← hrk], by rw [← hq, ← hrk], L, N, ε, e₁, fun _ => rfl, ψ, hcompl, hψ,
    rfl, fun _ => rfl, htor, hdiv₁⟩⟩, ⟨rfl, hbd⟩, hθ, yo, κ, h₃, h₄, h₅⟩

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_family_through_degenerating_family : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  first | exact @GlobalTheory.UCanon.exists_canon_through | exact GlobalTheory.UCanon.exists_canon_through | (intros; apply GlobalTheory.UCanon.exists_canon_through <;> assumption)
end

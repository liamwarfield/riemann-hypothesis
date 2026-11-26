module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKSubgroupTwist
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.KTwist

open GlobalTheory.KerPow

section General

variable {X Y B : Scheme.{0}} {N N' : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem gen_div_of_gen {M M' : LB Y} (h : ∃ t : LB.Gen M, t.IsGen) (h' : ∃ t : LB.Gen M', t.IsGen) :
    ∃ t : LB.Gen (LB.div M M'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  refine ⟨⟨fun p => res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : M.ι × M'.ι, y ∈ M.U p.1 ⊓ M'.U p.2 → gm (𝟙 Y) y (M.U p.1 ⊓ M'.U p.2)
      (res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹) =
      gm (𝟙 Y) y _ (t.s p.1) * (gm (𝟙 Y) y _ (t'.s p.2))⁻¹ := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))
  have tr : ∀ {A : LB Y} {a : LB.Gen A}, a.IsGen → ∀ i j, y ∈ A.U i ⊓ A.U j →
      gm (𝟙 Y) y _ (a.s i) = gm (𝟙 Y) y _ (A.g i j) * gm (𝟙 Y) y _ (a.s j) := fun ha i j hm =>
    (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ha i j)).trans
      ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hm _))))
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div M' M (𝟙 Y) y p q hy) ((gm_res _ y _ hy _).trans (v q hy.2)))).symm)
  rw [tr ht p.1 q.1 ⟨hy.1.1, hy.2.1⟩, tr ht' p.2 q.2 ⟨hy.1.2, hy.2.2⟩, mul_inv, _root_.mul_mul_mul_comm]

theorem hasGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) (h' : HasGen N' φ ε) :
    HasGen (LB.div N N') φ ε ↔ HasGen N φ ε := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u', hu'⟩ := h'
    obtain ⟨u, hu, -⟩ := DescendedPrincipal.exists_gen_mul_div hN hN' u' hu' q hq
    exact ⟨u, hu⟩
  · intro h
    obtain ⟨w, hw⟩ := gen_div_of_gen h h'
    exact gen_chartPull (DescendedPrincipal.chartPullDiv N N' φ ε) w hw

theorem locGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) {π : Y ⟶ B} (h' : LocGen N' π φ ε) :
    LocGen (LB.div N N') π φ ε ↔ LocGen N π φ ε := by
  have shrink : ∀ {A : LB X} {V W : B.Opens}, W ≤ V → HasGen A (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε →
      HasGen A (fun k => (π ⁻¹ᵁ W).ι ≫ φ k) ε := fun {A V W} hle t =>
    t.pull (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun _ h => hle h))
      (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  constructor <;> intro H p <;> obtain ⟨V, hV, t⟩ := H p <;> obtain ⟨V', hV', t'⟩ := h' p
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).1 (shrink inf_le_left t)⟩
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).2 (shrink inf_le_left t)⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S}

theorem inK_div_iff {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) {x : T ⟶ B} (hx : InK B O x) :
    InK B (LB.div L O) x ↔ InK B L x :=
  (inK_iff_locGen x).trans ((locGen_div_iff hL hO ((inK_iff_locGen x).1 hx)).trans (inK_iff_locGen x).symm)

theorem inK_of_lam [IsCommMonObj B] {O : LB B.left} (hO : O.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen)
    (x : T ⟶ B) : InK B O x := by
  have H₀ : HasGen O (PrimCocycle.lamφ B) PrimCocycle.lamε := hu
  have H₁ : LocGen O (fst T B).left
      (fun I => (lift (fst T B ≫ x) (snd T B)).left ≫ PrimCocycle.lamφ B I) PrimCocycle.lamε := fun _ =>
    ⟨⊤, trivial, H₀.pull (((fst T B).left ⁻¹ᵁ ⊤).ι ≫ (lift (fst T B ≫ x) (snd T B)).left)
      fun _ => Category.assoc _ _ _⟩
  have H₂ := BoxKernel.locGen_base hO (fst T B).left (K := Fin 2) ![x.left, (1 : T ⟶ B).left] ![-1, 1]
  refine (inK_iff_locGen x).2 (H₁.comb hO H₂ fun U _ h => ?_)
  rw [PrimCocycle.prod_lam (fst T B ≫ x) (snd T B) h, Fin.prod_univ_two, Fin.prod_univ_two]
  have e₁ : (fst T B).left ≫ (1 : T ⟶ B).left = (1 : T ⊗ B ⟶ B).left :=
    congrArg (fun q : T ⊗ B ⟶ B => q.left) (MonObj.comp_one (fst T B))
  show h (translPt B x).left * (h ((fst T B).left ≫ x.left))⁻¹ * (h (snd T B).left)⁻¹ * h (1 : T ⊗ B ⟶ B).left *
      (h ((fst T B).left ≫ x.left) ^ (-1 : ℤ) * h ((fst T B).left ≫ (1 : T ⟶ B).left) ^ (1 : ℤ))⁻¹ =
    h (translPt B x).left ^ (1 : ℤ) * h (snd T B).left ^ (-1 : ℤ)
  rw [e₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.UU.KTwist

namespace GlobalTheory.UU

end GlobalTheory.UU

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem kTriv_of_lamEq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L L' : LB A.left), L.IsLB → L'.IsLB → LamEq L' (𝟙 A) (𝟙 A) L (𝟙 A) (𝟙 A) → Out.KTriv A L → Out.KTriv A L' := by
  intro S A _ _ L L' hL hL' h hK R _ t x hx
  have hu : ∃ u : LB.Gen (abelian₂ A (LB.div L L')), u.IsGen := by
    simp only [LamEq, Category.comp_id] at h
    obtain ⟨w, hw⟩ := h
    exact gen_chartPull (GlobalTheory.DescendedPrincipal.chartPullDiv L L' _ _) w hw
  exact hK R t x ((GlobalTheory.UU.KTwist.inK_div_iff (x := x) hL hL' hx).1 (GlobalTheory.UU.KTwist.inK_of_lam (LB.isLB_div hL hL') hu x))

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MapRtEqNegIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem map_rt_eq_neg_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {R : Type} [CommRing R]
    [CharZero R] {ρ : R} (hρ : ρ ^ 2 = -(H.d : R)) {k : Type} [Field k] (β : R →+* k) (hβ : Function.Injective β)
    (τ : 𝓞 E →+* k) : τ H.rt = β (-ρ) ↔ τ H.rt ≠ β ρ := by
  have h1 : (τ H.rt) ^ 2 = (β ρ) ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, hρ]; simp
  have h2 : β (-ρ) ≠ β ρ := by
    intro h
    have h3 : -ρ = ρ := hβ h
    have h4 : ((2 * H.d : ℕ) : R) = 0 := by
      push_cast
      linear_combination 2 * hρ + ρ * h3
    have h5 : 2 * H.d = 0 := Nat.cast_eq_zero.mp h4
    have := H.d_prime.pos
    omega
  constructor
  · intro h h'
    exact h2 (h.symm.trans h')
  · intro h
    rw [map_neg]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left h

theorem hasType_neg_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (G : Over (Sp R)) [GrpObj G] (act : OAct (𝓞 E) G) (ρ : R) (p q : ℕ), ρ ^ 2 = -(H.d : R) → (HasType H act ρ p q ↔ HasType H act (-ρ) q p) := by
  intro E _ _ _ H R _ _ G _ act ρ p q hρ
  unfold HasType
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun β =>
    forall_congr' fun hβ => forall_congr' fun τ => ?_
  have h := map_rt_eq_neg_iff H hρ β hβ τ
  rw [ne_eq (τ H.rt) (β (-ρ)), h, not_not]
  exact and_comm

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_natCast_pow {v : epsR R ⟶ G} (hv : IsTangent v) (n : ℕ) :
    IsLieComb ![(n : R)] ![v] (v ^ n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.2 hv
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    exact (lieMultiple_calculus R G G v _ v n 1).2.1 hv ih
      (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.1

theorem isMonHom_id_pow [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem quadratic_equation_of_derivative : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (W : P.A ⟶ P.A) (w : k) (n : ℕ), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom W → IsLieComb ![w] ![v] (v ≫ W) → w * w + n = w → (W ≫ W) * (𝟙 P.A) ^ n = W := by
  intro hT hB k _ s P v W w n hv hb hW hw heq
  have hc := P.isAb.comm
  have h1 := isMonHom_id_pow (G := P.A) n
  have h2 : IsMonHom ((W ≫ W) * (𝟙 P.A) ^ n) :=
    inferInstanceAs (IsMonHom (lift (W ≫ W) ((𝟙 P.A) ^ n) ≫ μ[P.A]))
  refine GlobalTheory.T.curve_hom_ext_of_derivative_lieBasis hT hB k s P P v _ _ hb h2 hW ?_
  have h3 : IsLieComb ![w] ![v ≫ W] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ v w w).2.2.2.1 W hw
  have h4 : IsLieComb ![w * w] ![v] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ _ w w).2.2.1 hw h3
  have h5 : IsLieComb ![w * w + n] ![v] (((v ≫ W) ≫ W) * v ^ n) :=
    (lieMultiple_calculus k P.A P.A v _ _ (w * w) n).2.1 hv h4 (isLieComb_natCast_pow hv n)
  rw [heq, isLieComb_one_iff_comp] at h5
  rw [isLieComb_one_iff_comp] at hw
  rw [MonObj.comp_mul, MonObj.comp_pow, Category.comp_id, ← Category.assoc, h5, ← hw]

end GlobalTheory.LieMultiple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open PureTypeVector in
theorem cmDatum_form_sqrtNegD_pure_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {ρ : ℂ}
    (hty : ∀ i, ty i (H.rt : E) = ρ) {x : D.La} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ρ.im * r := by
  obtain ⟨hlin, hinj, -, -, Hm, hH, hpos, hEF⟩ := hP
  have hw0 : Pe (H.w0 • x) = ((1 + ρ) / 2) • Pe x := by
    funext i
    rw [hlin, Pi.smul_apply, smul_eq_mul]
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simpa [map_ofNat] using this
    have h3 := congrArg (ty i) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hty i] at h3
    rw [← h3]; ring
  set r : ℝ := (hermForm Hm (Pe x) (Pe x)).re with hr
  have hre : hermForm Hm (Pe x) (Pe x) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [hermForm_self_im hH])
  have hr0 : 0 < r := hpos _ fun h => hx (hinj (by rw [h, map_zero]))
  refine ⟨r / 2, by positivity, ?_⟩
  rw [← hEF, hw0]
  have := hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [this, hre]
  simp
  ring

theorem definite_datum_form_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ),
      (D.q = 0 ∧ 0 < ((ε : ℤ) : ℝ) * H.rt0.im) ∨ (D.p = 0 ∧ ((ε : ℤ) : ℝ) * H.rt0.im < 0) →
      ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := by
  intro E _ _ _ H D ε h x hx
  obtain ⟨g, ty, hty⟩ : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
    have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩⟩
  obtain ⟨Pe, hP⟩ := datum_exists_period E H D g ty hty
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := fun i =>
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    Nat.card_pos.ne'
  have key : ∃ ρ : ℂ, (∀ i, ty i (H.rt : E) = ρ) ∧ 0 < ((ε : ℤ) : ℝ) * ρ.im := by
    rcases h with ⟨hq, hε⟩ | ⟨hp, hε⟩
    · refine ⟨H.rt0, fun i => ?_, hε⟩
      by_contra hne
      exact hcard i (((hty (ty i)).2 hne).trans hq)
    · refine ⟨-H.rt0, fun i => ?_, by simpa using hε⟩
      have hne : ty i (H.rt : E) ≠ H.rt0 := fun he => hcard i (((hty (ty i)).1 he).trans hp)
      have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
        have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
        simpa using this
      have h3 : ty i (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, h2, H.sqrt_neg_disc_sq]; simp
      exact (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left hne
  obtain ⟨ρ, hρ, hε⟩ := key
  obtain ⟨r, hr, hE⟩ := cmDatum_form_sqrtNegD_pure_period D hP hρ hx
  have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((D.EF (H.w0 • x) x : ℤ) : ℝ) := by
    rw [hE, ← _root_.mul_assoc]; exact mul_pos hε hr
  exact_mod_cast this

end GlobalTheory.CM
end

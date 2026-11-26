module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LatData

section General

variable {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem exists_span_smul_mem {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ (v : Fin r → M) (c : R), c ≠ 0 ∧ ∀ m : M, ∃ s : Fin r → R, c • m = ∑ i, s i • v i := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  refine ⟨v, c, nonZeroDivisors.ne_zero hc0, fun m => ?_⟩
  have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_range_iff_exists_fun] at h3
  obtain ⟨s, hs⟩ := h3
  exact ⟨s, hs.symm⟩

theorem finrank_add_le_of_disjoint {A B : Submodule R M} (h : Disjoint A B) :
    Module.finrank R A + Module.finrank R B ≤ Module.finrank R M := by
  have h1 := A.finrank_quotient_add_finrank
  have h2 : Module.finrank R B ≤ Module.finrank R (M ⧸ A) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := A.mkQ ∘ₗ B.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    exact Subtype.ext (Submodule.disjoint_def.1 h _ ((Submodule.Quotient.mk_eq_zero A).1 hb) b.2)
  omega

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := fun h => by
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have := H.sqrt_neg_disc_sq
  rw [h0] at this
  exact H.d_prime.ne_zero (by simpa using this)

theorem exists_embedding (H : Host E) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : ∃ τ : E →+* ℂ, τ (H.rt : E) = ρ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans hρ.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    have hre : ρ.re = 0 := by
      have e1 := congrArg Complex.re hρ
      have e2 := congrArg Complex.im hρ
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
      simp [pow_two] at e1 e2
      have e3 : ρ.re * ρ.im = 0 := by linarith
      rcases mul_eq_zero.1 e3 with e | e
      · exact e
      · rw [e] at e1
        nlinarith [mul_self_nonneg ρ.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

theorem card_le_finrank_lat {ρ ρ' : ℂ} (hne : ρ ≠ ρ') {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP ρ ⊔ PureType.lat hP ρ') {τ : E →+* ℂ} (hτ : τ (H.rt : E) = ρ) :
    Nat.card {i // ty i = τ} ≤ Module.finrank (𝓞 E) (PureType.lat hP ρ) := by
  classical
  have := D.fin
  obtain ⟨v, c, hc, hv⟩ := exists_span_smul_mem (R := 𝓞 E) (M := PureType.lat hP ρ) rfl
  let pr : (Fin g → ℂ) →ₗ[ℂ] ({i // ty i = τ} → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  have hsm : ∀ (s : 𝓞 E) (a : D.La), pr (Pe (s • a)) = τ (s : E) • pr (Pe a) := fun s a => by
    funext i
    simp only [pr, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
    rw [hP.1, i.2]
  let W : Submodule ℂ ({i // ty i = τ} → ℂ) := Submodule.span ℂ (Set.range fun i => pr (Pe (v i)))
  have h1 : ∀ a : PureType.lat hP ρ, pr (Pe a) ∈ W := fun a => by
    obtain ⟨s, hs⟩ := hv a
    have hc' : τ (c : E) ≠ 0 := by simpa using hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← W.smul_mem_iff hc', ← hsm, ← Submodule.coe_smul, hs, Submodule.coe_sum, map_sum, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [Submodule.coe_smul, hsm]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ a : D.La, pr (Pe a) ∈ W := fun a => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hs a)
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hy0 : pr (Pe y) = 0 := funext fun i => hy i (by rw [i.2, hτ]; exact hne)
    rw [← W.smul_mem_iff hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul, ← hxy, map_add (f := _), map_add (f := _), hy0,
      add_zero]
    exact h1 ⟨x, hx⟩
  have h3 : W = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨z, rfl⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ
      (Subtype.val : {i // ty i = τ} → Fin g) Subtype.val_injective w
    have hz : z ∈ Submodule.span ℝ (Set.range Pe) := by rw [hP.2.2.2.1]; trivial
    have : Submodule.span ℝ (Set.range Pe) ≤ (W.comap pr).restrictScalars ℝ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h2 a)
    exact this hz
  have h4 := finrank_le_of_span_eq_top h3
  simpa [Nat.card_eq_fintype_card] using h4

theorem finrank_lat (ht : IsTypeFn H D.p D.q ty) {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP H.rt0 ⊔ PureType.lat hP (-H.rt0)) :
    Module.finrank (𝓞 E) (PureType.lat hP H.rt0) = D.p ∧
      Module.finrank (𝓞 E) (PureType.lat hP (-H.rt0)) = D.q := by
  have := D.fin
  have hne := rt0_ne_neg H
  obtain ⟨τ, hτ⟩ := exists_embedding H H.sqrt_neg_disc_sq
  obtain ⟨τ', hτ'⟩ := exists_embedding H (ρ := -H.rt0) (by rw [neg_sq, H.sqrt_neg_disc_sq])
  have h1 := card_le_finrank_lat hP hne hn hs hτ
  have h2 := card_le_finrank_lat hP hne.symm hn (fun a => sup_comm (PureType.lat hP H.rt0) _ ▸ hs a) hτ'
  rw [(ht τ).1 hτ] at h1
  rw [(ht τ').2 (by rw [hτ']; exact hne.symm)] at h2
  have h3 := finrank_add_le_of_disjoint (PureType.disjoint_lat hP hne)
  rw [D.rank] at h3
  omega

end GlobalTheory.CM.LatData

namespace GlobalTheory.CM

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TateIsoExistsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExtStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionFieldExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_torsion_fieldExt : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  intro hL S _ P k k' _ _ _ _ _ j t
  let h : Over.mk (spMap j ≫ t) ⟶ Over.mk t := Over.homMk (spMap j) rfl
  let r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A) :=
    { toFun := fun x => h ≫ x, map_one' := comp_one _, map_mul' := fun x y => comp_mul _ _ _ }
  have hr : Function.Injective r := by
    letI := j.toAlgebra
    haveI : Flat (spMap j) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat k k')
    haveI : Surjective (spMap j) := ⟨fun p => ⟨(⊥ : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    haveI : Epi h.left := Flat.epi_of_flat_of_surjective (spMap j)
    haveI : Epi h := Over.epi_of_epi_left _
    exact fun x y e => (cancel_epi h).1 e
  have hu : ∀ c : kˣ, Units.map h.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
    fun c => Units.ext (congrArg (fun q => q.hom (c : k))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  have up : ∀ (n : ℕ) x y (c : kˣ), Out.WeilIs P.A P.L n x y (unitOn c) →
      Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c)) := fun n x y c H =>
    hu c ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h H
  refine ⟨r, fun _ => rfl, hr, fun n y hn hy => ?_, fun n x y c _ hx hy => ⟨up n x y c, fun H => ?_⟩⟩
  · have hk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : k') ≠ 0 := by rw [← map_natCast j]; exact (map_ne_zero j).2 hk
    have c₁ := (hL.mulN S P n hn).2.2.2.2 k t hk
    have c₂ := (hL.mulN S P n hn).2.2.2.2 k' (spMap j ≫ t) hk'
    let f : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (hr (congrArg Subtype.val e))
    haveI : Finite {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
    obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le (by rw [c₁, c₂])).2 ⟨y, hy⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩
  · obtain ⟨d, hd, -⟩ := (hL.weil S P n (Over.mk t)).1 x y hx hy
    let u : kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom d
    have e : unitOn u = d := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) d.val)
    rw [← e] at hd
    have e₁ := ((hL.weil S P n (Over.mk (spMap j ≫ t))).1 (r x) (r y) (by rw [← map_pow, hx, map_one])
      (by rw [← map_pow, hy, map_one])).unique (up n x y u hd) H
    have e₂ : u = c := Units.ext (j.injective
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k')).inv).1 (congrArg Units.val e₁)))
    exact e₂ ▸ hd

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_torsion_injective_weil_compatible : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  first | exact @GlobalTheory.exists_torsion_fieldExt | exact GlobalTheory.exists_torsion_fieldExt | (intros; apply GlobalTheory.exists_torsion_fieldExt <;> assumption)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_algClosure_lift {K k : Type} [Field K] [Field k] [IsAlgClosed k] (β : K →+* k) :
    ∃ j : AlgebraicClosure K →+* k, j.comp (algebraMap K (AlgebraicClosure K)) = β := by
  letI : Algebra K k := β.toAlgebra
  let f : AlgebraicClosure K →ₐ[K] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun z => f.commutes z⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}

def OnTors (e : ℕ → Q → Q → kˣ → Prop) (n : ℕ) (x y : Q) (c : kˣ) : Prop :=
  0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c

def tateIsoCongr {e e' : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    (h : ∀ n x y c, 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e' n x y c) : TateIso D k Q act e' :=
  { I with
    isom := fun n hn a b =>
      h n _ _ _ hn ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b) }

theorem onTors_iff {Ω Q' : Type} [Field Ω] [Group Q'] (i : k →+* Ω) (r : Q →* Q') (hr : Function.Injective r)
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}
    (h : ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
      (e n x y c ↔ e' n (r x) (r y) (Units.map i.toMonoidHom c))) (n : ℕ) (x y : Q) (c : kˣ) :
    OnTors e' n (r x) (r y) (Units.map i.toMonoidHom c) ↔ OnTors e n x y c := by
  unfold OnTors
  rw [← map_pow, ← map_pow, map_eq_one_iff r hr, map_eq_one_iff r hr]
  exact forall₃_congr fun hn hx hy => (h n x y c hn hx hy).symm

theorem onto_tors {Q' : Type} [Group Q'] (r : Q →* Q') (hr : Function.Injective r)
    (h : ∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) (n : ℕ) (hn : 0 < n) (z : Q') (hz : z ^ n = 1) :
    ∃ y : Q, y ^ n = 1 ∧ r y = z := by
  obtain ⟨x, rfl⟩ := h n z hn hz
  exact ⟨x, by rwa [← map_pow, map_eq_one_iff r hr] at hz, rfl⟩

end Abstract

theorem cmTorsionIsometry_transport_geometricPoint (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    (hm : ∀ c, IsMonHom (act c))
    {F Ω k : Type} [Field F] [Field Ω] [Field k] [IsAlgClosed F] [IsAlgClosed Ω] [IsAlgClosed k] [CharZero F]
    (i : F →+* Ω) (j : F →+* k) (x : Sp F ⟶ S) (y : Sp Ω ⟶ S) (z : Sp k ⟶ S)
    (hy : spMap i ≫ x = y) (hz : spMap j ≫ x = z)
    (I : TateIso D Ω (Over.mk y ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D k (Over.mk z ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      (∀ (n : ℕ) (u : F), 0 < n → (I.ζ n : Ω) = i u → (I'.ζ n : k) = j u) ∧
      ∀ (n : ℕ) a (s : 𝟙_ (Over S) ⟶ P.A), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  subst hy hz
  have key : ∀ (k' : Type) [Field k'] (l : F →+* k') (r : (Over.mk x ⟶ P.A) →* (Over.mk (spMap l ≫ x) ⟶ P.A)),
      (∀ y, (r y).left = spMap l ≫ y.left) →
      (∀ c y, r (y ≫ act c) = r y ≫ act c) ∧ ∀ s : 𝟙_ (Over S) ⟶ P.A, r (toUnit _ ≫ s) = toUnit _ ≫ s := by
    intro k' _ l r hr
    have h : ∀ y, r y = (Over.homMk (spMap l) rfl : Over.mk (spMap l ≫ x) ⟶ Over.mk x) ≫ y :=
      fun y => Over.OverMorphism.ext (hr y)
    exact ⟨fun c y => by rw [h, h, Category.assoc], fun s => by rw [h, ← Category.assoc, comp_toUnit]⟩
  obtain ⟨r, hr, rinj, ronto, rw'⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F Ω i x
  obtain ⟨q, hq, qinj, qonto, qw⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F k j x
  obtain ⟨I₀, h₀⟩ := TateIsoFieldExt.down D i r (act := fun c y => y ≫ act c)
    (e := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) rinj (onto_tors r rinj ronto)
    (key Ω i r hr).1 (fun c => by haveI := hm c; exact MonObj.one_comp (act c))
    (onTors_iff i r rinj rw') (tateIsoCongr I fun _ _ _ _ _ _ _ h _ _ _ => h)
  obtain ⟨I', h'⟩ := TateIsoFieldExt.up D j q (act' := fun c y => y ≫ act c)
    (e' := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) qinj (onto_tors q qinj qonto)
    (key k j q hq).1 (onTors_iff j q qinj qw) I₀
  refine ⟨tateIsoCongr I' fun _ _ _ _ hn hx hy h => h hn hx hy, fun n u hn hu => ?_, fun n a s hn hs => ?_⟩
  · have h1 : i (I₀.ζ n) = i u := (h₀ n hn).1.symm.trans hu
    exact (h' n hn).1.trans (congrArg j (i.injective h1))
  · have h1 : toUnit _ ≫ s = I₀.ev n a :=
      rinj (((key Ω i r hr).2 s).trans (hs.trans ((h₀ n hn).2 a)))
    exact ((key k j q hq).2 s).symm.trans ((congrArg q h1).trans ((h' n hn).2 a).symm)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamF

theorem pnsmulPt_eq_frozen {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (n : ℕ) (x : T ⟶ G) :
    pnsmulPt n x = Formalism.L2.Pj.abelian₂.pnsmulPt n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pnsmulPt, Formalism.L2.Pj.abelian₂.pnsmulPt, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

@[reducible] def LamObj.toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

@[reducible] def LamObj.ofFrozen (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') : LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

theorem rosatiConj_iff_frozen {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) :
    RosatiConj A oa ↔ Formalism.L2.Pj.abelian₂.RosatiConj A oa := by
  simp only [RosatiConj, Formalism.L2.Pj.abelian₂.RosatiConj, pnsmulPt_eq_frozen]

theorem isIsogSum_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.IsIsogSum o.toFrozen ↔ IsIsogSum o := by
  simp only [IsIsogSum, Formalism.L2.Pj.abelian₂.IsIsogSum, pnsmulPt_eq_frozen]
  rfl

theorem polClause_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.PolClause o.toFrozen ↔ PolClause o := by
  simp only [PolClause, Formalism.L2.Pj.abelian₂.PolClause, pnsmulPt_eq_frozen]

theorem fixed_of_lambdaBundle_objectCondition (o : LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    Formalism.L2.Pj.abelian₂.LamObjGood o.toFrozen f La ↔ LamObjGood o f La := by
  unfold LamObjGood Formalism.L2.Pj.abelian₂.LamObjGood
  rw [isIsogSum_toFrozen, polClause_toFrozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen]
  rfl

theorem lambdaBundle_objectCondition_of_fixed (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    LamObjGood (LamObj.ofFrozen o) f La ↔ Formalism.L2.Pj.abelian₂.LamObjGood o f La :=
  (fixed_of_lambdaBundle_objectCondition (LamObj.ofFrozen o) f La).symm

@[reducible] def LamLetters.toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : Formalism.L2.Pj.abelian₂.LamLetters o.toFrozen where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

@[reducible] def LamLetters.ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    LamLetters (LamObj.ofFrozen o) where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

theorem LamLetters.isLetter_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) (k : Fin o.xB.P.g)
    (w : epsR o.K₁ ⟶ o.xB.P.A) : L.toFrozen.IsLetter k w ↔ L.IsLetter k w := by
  unfold LamLetters.IsLetter Formalism.L2.Pj.abelian₂.LamLetters.IsLetter
  dsimp only
  cases L.src k <;> rfl

theorem LamLetters.isGood_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : L.toFrozen.IsGood ↔ L.IsGood := by
  unfold LamLetters.IsGood Formalism.L2.Pj.abelian₂.LamLetters.IsGood
  refine and_congr Iff.rfl (and_congr (forall_congr' fun b => forall_congr' fun i => ?_)
    (and_congr (forall_congr' fun k => exists_congr fun w => and_congr (L.isLetter_toFrozen k w) Iff.rfl)
      (forall_congr' fun k => ?_)))
  · dsimp only
    cases L.src (L.e ⟨b, i⟩) <;> rfl
  · dsimp only
    cases L.src k <;> rfl

theorem LamLetters.isGood_ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    (LamLetters.ofFrozen L).IsGood ↔ L.IsGood :=
  (LamLetters.isGood_toFrozen (LamLetters.ofFrozen L)).symm

omit [StarRing (𝓞 E)] in
theorem lambdaBundle_degree_iff (H : Host E) (x : ℝ) : LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x :=
  ⟨fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho),
   fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho)⟩

theorem lambdaBundle_index_iff : LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_length_iff : LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_conditions_iff :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ),
      GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧
    (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) :=
  ⟨fun _ _ _ _ H x => lambdaBundle_degree_iff H x, lambdaBundle_index_iff, lambdaBundle_length_iff⟩

end GlobalTheory.LamF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibraryStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLieStatements_iff_library : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ), GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧ (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) := by
  first | exact @GlobalTheory.LamF.lambdaBundle_conditions_iff | exact GlobalTheory.LamF.lambdaBundle_conditions_iff | (intros; apply GlobalTheory.LamF.lambdaBundle_conditions_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.ThetaDegree

def IsPullOf {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (t : LB.Gen (P.L.pull (eSec P.A))) (θ : P.L.Sec) (y : KeyIn R) : Prop :=
  ∃ (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧
    PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => eSec P.A) (fun _ => 1) y.rig t (spMap f) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ y.P.A.left) (z : Z) j k, ψ (r z) ∈ P.L.U j → r z ∈ y.P.L.U k →
      gs (r ≫ ψ) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (y.th.f k)

theorem exists_isPullOf {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (hg : 1 ≤ P.g) {t : LB.Gen (P.L.pull (eSec P.A))} (ht : t.IsGen) (θ : P.L.Sec)
    (hθ : ∀ s : Sp R, ∃ z, P.A.hom z = spMap f s ∧ z ∈ Out.nonzeroLocus θ) : ∃ y : KeyIn R, IsPullOf f P t θ y := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he P.L t).IsGen :=
    Out.LBxP.isGen_pullAlong P.L φ (spMap f) (fun _ : PUnit => eSec P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) t ht
  obtain ⟨th', hth'⟩ := sec_pull_down hw P.isLB hL' θ
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P'.A P'.smoothDim
  refine ⟨⟨P', hg, _, hr, th', fun s => ?_, v, hv⟩, φ, idIso _, rfl, h, hw,
    (maps_iff (idIso _) (fun _ => eSec P'.A) (fun _ => eSec P.A) _ _ t (spMap f) _ (rigPull_le φ (spMap f) he P.L)
      (fun _ => rfl)).1 (fun p => hr p.1 p.2), hth'⟩
  obtain ⟨z, hz, hz'⟩ := hθ s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (θ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem IsPullOf.exists_keyPB {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [CommRing R'] {f : O →+* R}
    {g : R →+* R'} {P : Out.PolAV (Sp O)} {t : LB.Gen (P.L.pull (eSec P.A))} {θ : P.L.Sec} {y : KeyIn R} {x : KeyIn R'}
    (hy : IsPullOf f P t θ y) (hx : IsPullOf (g.comp f) P t θ x) :
    ∃ v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ y g := by
  obtain ⟨ψ, w, hg, hc, hw, hr, hs⟩ := hy
  obtain ⟨φ'', w'', hg'', hc'', hw'', hr'', hs''⟩ := hx
  have hsp : spMap (g.comp f) = spMap g ≫ spMap f := (spMap_comp_spMap f g).symm
  obtain ⟨φ, rfl, hw0⟩ : ∃ φ : x.P.A.left ⟶ y.P.A.left, φ ≫ ψ = φ'' ∧ φ ≫ y.P.A.hom = x.P.A.hom ≫ spMap g :=
    ⟨hc.1.lift φ'' (x.P.A.hom ≫ spMap g) (by rw [hc''.1.w, Category.assoc, hsp]), hc.1.lift_fst _ _ _,
      hc.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap g) φ := hc.cancel (hc''.congr hsp rfl) hw0
  have he : eSec x.P.A ≫ φ = spMap g ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' hw hw'' y.P.isLB x.P.isLB
  rw [hsp] at hr''
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR g) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap g := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR g) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange g h y.basis hv'
  have hg' : x.P.g = y.P.g := hg''.trans hg.symm
  refine ⟨_, hb hg', φ, he, w', hg', Chart.dualMapR g, h, (isGen_iff _).2 (T.pgen_cancel P.isLB hw hw''),
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel P.isLB (fun _ => he) hr hr''),
    KeyPow.appLE_eq_of_stalk _ y.th x.th fun z i k hi hk => ?_, fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨j, hj⟩ := exists_chart P.isLB (ψ (φ z))
    have a := hs _ (𝟙 _ ≫ φ) z j i hj hi
    have b := hs'' _ (𝟙 _) z j k hj hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_sec_generic (hT : Out.SecTwistSt) {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (P : Out.PolAV (Sp O)) {X : Scheme.{0}} {φ : X ⟶ P.A.left} {q : X ⟶ Sp K}
    (hp : IsPullback φ q P.A.hom (spMap (algebraMap O K))) : ∃ (θ : P.L.Sec) (z : X), φ z ∈ Out.nonzeroLocus θ := by
  have := P.isAb.smooth
  have := P.isAb.proper
  obtain ⟨s, hs⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread hp P.isLB s
  obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hk' : φ z ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  have hu : IsUnit (gs φ z _ (θ.f (k PUnit.unit))) := by
    rw [hθ _ z hk']
    exact (SecSpread.isUnit_cst hp.w z hd).mul u
  rw [gs_stalkMap φ z _ hk', isUnit_map_iff] at hu
  exact ⟨θ, z, (mem_nonzeroLocus _ _).2 ⟨_, hk', hu⟩⟩

variable {K : Type} [Field K] [NumberField K]

theorem exists_scalar (hT : Out.SecTwistSt) (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left)
    (w : LB.Iso x.P.L (P.L.pull φ)) (hg : x.P.g = P.g)
    (hφ : IsGrpPullback x.P.A P.A (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) :
    ∃ a : K, a ≠ 0 ∧ {𝔭 | ¬ ∃ M, KeyPow.IsLocalModel x 𝔭 a M}.Finite := by
  have := P.isAb.smooth
  obtain ⟨θ, z₀, hz₀⟩ := exists_sec_generic hT P hφ.1
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale P.isLB x.P.isLB ((isGen_iff _).1 hw) (p := x.P.A.hom) (Over.w η[x.P.A])
    (PolBaseChange.eSec_comm hφ) x.rig_gen ht
  obtain ⟨th', hth'⟩ := sec_pull_down g' P.isLB x.P.isLB θ
  have hne : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th' := fun s => by
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz₀
    obtain ⟨k, hk⟩ := exists_chart x.P.isLB z₀
    refine ⟨z₀, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ z₀ _ (θ.f j)) := by rw [gs_stalkMap φ z₀ _ hj]; exact u.map _
    have e := hth' _ (𝟙 _) z₀ j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  let x' : KeyIn K := ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hne, x.v, x.basis⟩
  have hx' : IsPullOf (algebraMap (𝓞 K) K) P t θ x' := ⟨φ, w', hg, hφ, g', m', hth'⟩
  obtain ⟨a, -, ha, -⟩ := KeyPow.exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis x.basis
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem P.A.hom hz₀) (P.A.hom.isOpenMap _ (Out.nonzeroLocus θ).isOpen)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hd (Ideal.zero_mem _)
  refine ⟨a, ?_, (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0)).subset fun 𝔭 h𝔭 => ?_⟩
  · rintro rfl
    obtain ⟨z, -, hz⟩ := hne (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  by_contra hn
  refine h𝔭 ?_
  have hv : 𝔭.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    refine (𝔭.valuation_le_one d).antisymm (not_lt.1 fun h => hn ?_)
    exact (𝔭.valuation_lt_one_iff_dvd d).1 h
  let R := (𝔭.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
  have hu : IsUnit (f d) := (Valuation.integer.integers (𝔭.valuation K)).isUnit_iff_valuation_eq_one.2 hv
  obtain ⟨y, hy⟩ := exists_isPullOf f P (hg ▸ x.g_pos) ht θ fun s => by
    have hs : spMap f s ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (𝓞 K))) := fun h =>
      s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f d ∈ s.asIdeal from h) hu)
    obtain ⟨z, h₁, h₂⟩ := hsub hs
    exact ⟨z, h₂, h₁⟩
  obtain ⟨v', hv', hPB⟩ := hy.exists_keyPB (g := algebraMap R K) (x := x') hx'
  choose M hM using fun i => (x.basis.2 _ (hv'.1 i)).exists
  exact ⟨M, R, _, inferInstance, inferInstance, _,
    inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hne, v', hv', fun r => r.2, ha, hM, hPB⟩

theorem exists_isThetaDeg : Out.SecTwistSt → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth), ∃ δ : ℝ, IsThetaDeg (F.key hg rig hr th hth) δ := by
  intro hT hU K _ _ P F hg rig hr th hth
  classical
  obtain ⟨e, hφ, hL⟩ := F.fib
  obtain ⟨w, hw⟩ := LBIso.symm hL
  let x := F.key hg rig hr th hth
  obtain ⟨oa, od, hloc⟩ := KeyPow.exists_isLocalModel_of_integral hT K P x F.φ w e hφ hw
  obtain ⟨a, ha, hfin⟩ := exists_scalar hT P x F.φ w e hφ hw
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K a = WithZero.exp (- -WithZero.log (𝔭.valuation K a)) :=
    fun 𝔭 => by rw [neg_neg, WithZero.exp_log (by simpa using ha)]
  refine ⟨_, fun 𝔭 => if ∃ M, KeyPow.IsLocalModel x 𝔭 a M then -WithZero.log (𝔭.valuation K a) else oa 𝔭, nth,
    fun 𝔭 => ?_, fun σ => ?_, (hfin.union (KeyPow.sum_log_norm_eq_finsum ha _ hv).1).subset fun 𝔭 h => ?_, rfl⟩
  · by_cases h : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · obtain ⟨M, hM⟩ := id h
      exact ⟨a, M, hM, by beta_reduce; rw [if_pos h]; exact hv 𝔭⟩
    · obtain ⟨a', M, hM, h₁, -⟩ := hloc 𝔭
      exact ⟨a', M, hM, by beta_reduce; rw [if_neg h]; exact h₁⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩
  · by_cases h' : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · exact Or.inr (by simpa only [Function.mem_support, if_pos h'] using h)
    · exact Or.inl h'

end GlobalTheory.ThetaDegree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal
noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors

namespace GlobalTheory.CM

theorem _root_.GlobalTheory.CM.deg_ideal_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (Λ : Submodule (𝓞 K) V) {v : V} (hv : v ≠ 0)
    {m : (K →+* ℂ) → ℝ} (hm : ∀ s, 0 < m s) (hf : ∀ s, (h.form s v v).re = m s)
    {𝔠 : FractionalIdeal (𝓞 K)⁰ K} (h𝔠 : 𝔠 ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔠) :
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ K - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K m / 2 := by
  set φ : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K) with hφ
  have hφapp : ∀ t, φ t = t • v := fun t => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    simp only [hφapp] at hab
    exact smul_left_injective K hv hab
  have hΛmap : Λ = (𝔠 : Submodule (𝓞 K) K).map φ := by
    ext z
    rw [hΛ, Submodule.mem_map]
    constructor
    · rintro ⟨t, rfl, ht⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, rfl, ht⟩
  have hform : ∀ s, h.form s v v = (m s : ℂ) := by
    intro s
    have hc := h.conj_symm s v v
    apply Complex.ext
    · simp [hf s]
    · simp only [Complex.ofReal_im]
      exact Complex.conj_eq_iff_im.mp hc
  have hcFG : (𝔠 : Submodule (𝓞 K) K).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠
  obtain ⟨r, w, hw⟩ := _root_.ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg (𝔠 : Submodule (𝓞 K) K) hcFG
  have hw' := hw
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hw'
  obtain ⟨hwmem, hwli, hwspan⟩ := hw'
  have hrange : Set.range (fun i => φ (w i)) = φ '' Set.range w := Set.range_comp φ w
  have hframe : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K Λ (fun i => φ (w i)) := by
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hΛmap]; exact Submodule.mem_map_of_mem (hwmem i)
    · exact hwli.map' (LinearMap.toSpanSingleton K V v) (LinearMap.ker_toSpanSingleton K hv)
    · intro z hz
      rw [SetLike.mem_coe, hΛ] at hz
      obtain ⟨t, rfl, ht⟩ := hz
      have ht' : t ∈ Submodule.span K (Set.range w) := hwspan ht
      have hmem := Submodule.mem_map_of_mem (f := LinearMap.toSpanSingleton K V v) ht'
      rw [Submodule.map_span, ← Set.range_comp] at hmem
      exact hmem
  have hΛFG : Λ.FG := hΛmap ▸ hcFG.map φ
  have hrel : (Submodule.span (𝓞 K) (Set.range (fun i => φ (w i)))).toAddSubgroup.relIndex
      Λ.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex
      (𝔠 : Submodule (𝓞 K) K).toAddSubgroup := by
    rw [hΛmap, hrange, ← Submodule.map_span, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hgram : ∀ σ, h.gram σ (fun i => φ (w i)) = (_root_.GlobalTheory.lineHerm m hm).gram σ w := by
    intro σ
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram
    ext i j
    simp only [Matrix.of_apply, hφapp, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, hform]
    unfold _root_.GlobalTheory.lineHerm
    simp only
    ring
  calc _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily h Λ (fun i => φ (w i)) := _root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hΛFG hframe
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) w := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily
      rw [hrel]
      simp_rw [hgram]
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) :=
      (_root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily _ hcFG hw).symm
    _ = _ := _root_.GlobalTheory.deg_lineHerm m hm h𝔠

theorem _root_.GlobalTheory.CM.two_mul_deg_dual_line : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V)
    (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) →
    (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) →
    (∀ s, (h.form s v v).re = (s (τ β)).re * n s) →
    (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
    2 * _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) +
      Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
  intro E K V _ _ _ _ _ _ _ _ _ h Λ v τ 𝔞 β n h𝔞 hv hn hβ hf hΛ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    simpa using (hβ s).1
  set 𝔞' : FractionalIdeal (𝓞 E)⁰ E :=
    FractionalIdeal.spanSingleton (𝓞 E)⁰ β * _root_.GlobalTheory.conjFrac 𝔞 with h𝔞'def
  have h𝔞' : 𝔞' ≠ 0 :=
    mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
      (_root_.GlobalTheory.conjFrac_ne_zero h𝔞)
  obtain ⟨𝔟, h𝔟, h𝔟span, h𝔟log⟩ := _root_.GlobalTheory.exists_fractionalIdeal_eq_span_image τ h𝔞'
  have hm : ∀ s : K →+* ℂ, 0 < (s (τ β)).re * n s := fun s => mul_pos (hβ (s.comp τ)).1 (hn s)
  have hmemΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔟⁻¹ := by
    intro z
    rw [hΛ]
    refine exists_congr fun t => and_congr_right fun _ => ?_
    rw [FractionalIdeal.mem_inv_iff h𝔟]
    constructor
    · intro H y hy
      rw [← FractionalIdeal.mem_coe, h𝔟span] at hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, hx, rfl⟩ := hx
        rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [_root_.GlobalTheory.mem_conjFrac] at hz
        have key := H _ hz
        rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = IsCMField.complexConj E z from rfl,
          IsCMField.complexConj_apply_apply] at key
        exact (_root_.GlobalTheory.mem_one_fractionalIdeal_iff).2 key
      | zero => simp
      | add x y _ _ hx hy =>
        rw [mul_add, ← FractionalIdeal.mem_coe]
        rw [← FractionalIdeal.mem_coe] at hx hy
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [mul_smul_comm, ← FractionalIdeal.mem_coe]
        exact Submodule.smul_mem _ a hx
    · intro H b hb
      rw [← _root_.GlobalTheory.mem_one_fractionalIdeal_iff]
      apply H
      rw [← FractionalIdeal.mem_coe, h𝔟span]
      apply Submodule.subset_span
      refine ⟨β * IsCMField.complexConj E b, ?_, rfl⟩
      rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul]
      exact ⟨IsCMField.complexConj E b, _root_.GlobalTheory.cc_mem_conjFrac.2 hb, rfl⟩
  have hdeg := _root_.GlobalTheory.CM.deg_ideal_smul h Λ hv hm hf (inv_ne_zero h𝔟) hmemΛ
  have hsumE : ∑ s : E →+* ℂ, Real.log (s β).re = Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
    rw [← Real.log_prod (fun s _ => ne_of_gt (hβ s).1)]
    congr 1
    have hprodC : ((∏ s : E →+* ℂ, (s β).re : ℝ) : ℂ) = (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) := by
      push_cast
      have hre : ∀ s : E →+* ℂ, ((s β).re : ℂ) = s β := fun s =>
        Complex.ext (by simp) (by simp [(hβ s).2])
      simp_rw [hre]
      rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun s => s β) (fun σ => σ β)
        (fun s => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ β]
      simp
    have hprod : (∏ s : E →+* ℂ, (s β).re : ℝ) = ((Algebra.norm ℚ β : ℚ) : ℝ) := by
      exact_mod_cast hprodC
    rw [hprod, abs_of_pos]
    rw [← hprod]
    exact Finset.prod_pos fun s _ => (hβ s).1
  have hM : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / finrank ℚ E + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
    have hsplit : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
        _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => ((s.comp τ) β).re) + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Real.log_mul (ne_of_gt (hβ (s.comp τ)).1) (ne_of_gt (hn s))
    have hres := _root_.GlobalTheory.meanLog_comp τ (fun s : E →+* ℂ => (s β).re)
    rw [hsplit, hres, ← hsumE]
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
    rfl
  have hlog𝔞' : Real.log (FractionalIdeal.absNorm 𝔞' : ℝ) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| + Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
    rw [h𝔞'def, map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Real.log_mul, _root_.GlobalTheory.log_absNorm_conjFrac h𝔞]
    · exact abs_ne_zero.mpr (Rat.cast_ne_zero.mpr ((Algebra.norm_ne_zero_iff).mpr hβ0))
    · exact Rat.cast_ne_zero.mpr (fun h0 => _root_.GlobalTheory.conjFrac_ne_zero h𝔞
        (FractionalIdeal.absNorm_eq_zero_iff.mp h0))
  have hinv : -Real.log (FractionalIdeal.absNorm 𝔟⁻¹ : ℝ) / finrank ℚ K =
      Real.log (FractionalIdeal.absNorm 𝔟 : ℝ) / finrank ℚ K := by
    rw [map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]
  rw [hdeg, hinv, h𝔟log, hlog𝔞', hM]
  ring

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_deg_dual_line_cmIdeal : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) → (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) → (∀ s, (h.form s v v).re = (s (τ β)).re * n s) → (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
  2 * deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - meanLog K n := by
  first | exact @GlobalTheory.CM.two_mul_deg_dual_line | exact GlobalTheory.CM.two_mul_deg_dual_line | (intros; apply GlobalTheory.CM.two_mul_deg_dual_line <;> assumption)
end
end

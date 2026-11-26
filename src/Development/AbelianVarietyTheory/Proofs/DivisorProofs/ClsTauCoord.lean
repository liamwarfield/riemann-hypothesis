module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Order

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev unitsR (R : Type) [CommRing R] [IsDomain R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev QR (R : Type) [CommRing R] [IsDomain R] := (FractionRing R)ˣ ⧸ unitsR R

abbrev cls : (FractionRing R)ˣ →* QR R := QuotientGroup.mk' (unitsR R)

theorem cls_eq_iff (x y : (FractionRing R)ˣ) :
    cls x = cls y ↔ ∃ u : Rˣ, (x : FractionRing R) = (y : FractionRing R) * algebraMap R (FractionRing R) u := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, hz⟩
    exact ⟨u, by rw [← hz]; rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩

theorem cls_unit (u : Rˣ) : cls (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

variable [IsLocalRing R]

def tq (D : DegPre R) (a b : D.X) : QR R :=
  cls (psiCoord D (a + b)) * (cls (psiCoord D a))⁻¹ * (cls (psiCoord D b))⁻¹

theorem cls_tauCoord {D : DegPre R} {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    cls x = tq D a b := by
  obtain ⟨u, hu⟩ := GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a)
    (psiCoord_spec D b)
  have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u *
      (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by
    ext; rw [hu]; simp <;> ring
  rw [this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]

theorem tq_symm (D : DegPre R) (a b : D.X) : tq D a b = tq D b a := by
  simp only [tq, add_comm a b]; exact mul_right_comm _ _ _

theorem tq_add_left (D : DegPre R) (hB : D.TauBimult) (a z b : D.X) : tq D (a + z) b = tq D a b * tq D z b := by
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D z b
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''
  rw [one_smul] at hx''
  rw [← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]

def tqHom (D : DegPre R) (hB : D.TauBimult) (a : D.X) : D.X →+ Additive (QR R) :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (tq D a b)) fun b b' => by
    rw [tq_symm D a (b + b'), tq_add_left D hB, tq_symm D b a, tq_symm D b' a]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsDiscreteValuationRing R → ∀ (D D' : DegPre R), D'.TauBimult → D'.PsiEven → D.TauBimult → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ (c : Fin 8 → (D.X →+ D'.X)) (e : D'.X ≃+ (Fin 8 → D.X)), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → (∀ v a' b (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (e a' v) b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' a' (c v b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R)) → ∀ y r, PsiCoord D' y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr
  haveI := hR
  have hq : 0 ≤ qW W β (e y) := GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)
  refine ⟨hq, ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = e y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u := ⟨_, rfl⟩
  rw [← hsd] at hq ⊢
  have hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s) := by
    subst ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]
  have h1 : ∑ v, c v (t v) = y := by rw [ht, hsd]; exact hsum y
  have hy : -y = ∑ v, c v (-(t v)) := by
    rw [← h1]; simp only [map_neg, Finset.sum_neg_distrib]
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)
  have hcl : cls x' = tq D' y (-y) := cls_tauCoord hx'
  have hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v)) := by
    intro v
    obtain ⟨a, ha⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))
    obtain ⟨b, hb⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))
    obtain ⟨u, hu⟩ := hcomp v y (-(t v)) a b ha hb
    rw [← cls_tauCoord hb, hsd, ← cls_tauCoord ha]
    exact ((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm
  have hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v))) := by
    have := map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ
    rw [← hy] at this
    refine this.trans ?_
    exact Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)
  obtain ⟨w0, hw0⟩ := GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow two_ne_zero, mul_zero] at hw0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm
  let ru : (FractionRing R)ˣ := toUnitK r hr0
  have hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0 := by
    ext; simp [ru, toUnitK, hw0]
  have hcr : cls ru ^ 2 = (cls x')⁻¹ := by
    have := congrArg cls hru
    rw [map_mul, map_pow, cls_unit] at this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq
  rw [hn, Int.toNat_natCast]
  have final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) →
      cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n) := by
    intro ρ hρ h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 h
    simp only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu
    have hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2) := ⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩
    exact (associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
      ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm
  by_cases hϖ : ϖ = 0
  · have hβ0 : ∀ a b, β a b = 0 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      by_contra h
      rw [hϖ, map_zero, zero_zpow _ h, mul_zero] at hu
      exact x.ne_zero hu
    have hq0 : qW W β s = 0 := by simp [qW, hβ0]
    have htq : ∀ a b, tq D a b = 1 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx]
      have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u := by
        ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl
      rw [this, cls_unit]
    have h1' : tq D' y (-y) = 1 := by
      apply Additive.ofMul.injective
      rw [hprod]; simp [htq]
    have hn0 : n = 0 := by omega
    subst hn0
    refine final 1 (by simp) ?_
    rw [hcr, hcl, h1']; simp
  · let ϖu : (FractionRing R)ˣ := toUnitK ϖ hϖ
    have htq : ∀ a b, tq D a b = cls ϖu ^ β a b := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx, ← map_zpow]
      exact (cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩
    have hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s)) := by
      rw [hcl]; apply Additive.ofMul.injective; rw [hprod]
      simp only [htq, ofMul_zpow]
      rw [← Finset.sum_smul, hsum2]
    refine final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_
    rw [hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]

end GlobalTheory.Poinc.E8Order
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommute
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaCommutant

theorem finrank_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) :
    Module.finrank F (EA P p N) = N ^ P.g := by
  obtain ⟨-, -, hdim, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have h := rank_eq_of_equiv_equiv (R := F) (R' := Γ((Over.mk p).left, ⊤)) σ j.symm σ.bijective
    (fun c w => j.injective (by rw [j.apply_symm_apply, hj, j.apply_symm_apply]))
  have h' : Module.finrank F (EA P p N) = Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) := by
    unfold Module.finrank
    simpa using congrArg Cardinal.toNat h
  rw [h', hdim]

theorem eq_smul_of_commute {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) (T : EA P p N →ₗ[F] EA P p N)
    (hT : ∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → IsActOf P.A P.L (N : ℤ) θ (T v).sec (T v').sec) :
    ∃ c : F, ∀ v, T v = c • v := by
  have hN1 : 0 < N := Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero])
  have hfr := finrank_eq P F p N hN
  have hpos : 0 < Module.finrank F (EA P p N) := by rw [hfr]; positivity
  haveI : Module.Finite F (EA P p N) := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial (EA P p N) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  obtain ⟨ρ, hact, -, hsame, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns S P (N : ℤ) (Over.mk p)
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have hσ : ∀ c : F, σ.symm (σ c) = c := σ.symm_apply_apply
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have key := hirr (Module.End.eigenspace T c) fun θ hθ v v' hvv hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    obtain ⟨θ₀, h₀, hcomm⟩ := hT θ.pt hθ
    obtain ⟨u, hu⟩ := hsame θ₀ θ h₀
    have e₁ : ρ θ (j.symm v) = j.symm v' := (hact θ _ _).1 hvv
    have e₂ : IsActOf P.A P.L (N : ℤ) θ₀ v.sec (j (ρ θ₀ (j.symm v))).sec := (hact θ₀ _ _).2 rfl
    have e₃ : ρ θ₀ (j.symm (T v)) = j.symm (T (j (ρ θ₀ (j.symm v)))) := (hact θ₀ _ _).1 (hcomm _ _ e₂)
    have e₄ : v' = σ.symm (u : Γ((Over.mk p).left, ⊤)) • j (ρ θ₀ (j.symm v)) := by
      rw [← hj, σ.apply_symm_apply, ← hu, e₁, j.apply_symm_apply]
    have e₅ : T (j (ρ θ₀ (j.symm v))) = c • j (ρ θ₀ (j.symm v)) := by
      have e₆ : j.symm (c • v) = σ c • j.symm v := rfl
      rw [← j.apply_symm_apply (T (j (ρ θ₀ (j.symm v)))), ← e₃, hv, e₆, map_smul, hj]
    rw [e₄, map_smul, e₅, smul_comm]
  rcases key with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · intro v
    exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)

end GlobalTheory.ThetaCommutant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum

theorem eqv_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'
  have hN1 : 1 ≤ N := hN.pos
  have hNF : (N : F) ≠ 0 := by
    have h1 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (N : FractionRing R) ≠ 0 := fun h =>
      h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))
    intro h
    apply h2
    apply (algebraMap (FractionRing R) F).injective
    rw [map_zero, map_natCast]
    exact_mod_cast h
  let p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R)) := jFK (R := R) F
  let mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R := R) F) A.A).left N, Eqv D.toPre A F N lab G →
      (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG =>
    { toFun := fun s => SecMod.mk _ (G s)
      map_add' := fun s t => DVR.SecOps.sec_ext fun j => hG.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => DVR.SecOps.sec_ext fun j =>
        hG.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff c s _).2 rfl) j }
  have hbij : ∀ G hG, Function.Bijective (mkE G hG) := fun G hG => hG.bij
  let e := LinearEquiv.ofBijective (mkE E hE) (hbij E hE)
  let T : EA A p N →ₗ[F] EA A p N := (mkE E' hE').comp e.symm.toLinearMap
  have hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s := fun s => by
    show mkE E' hE' (e.symm (e s)) = _
    rw [e.symm_apply_apply]
  obtain ⟨ρ, hact, -, -, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)
  have huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N),
      IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by
    have := ((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')
    exact DVR.SecOps.sec_ext fun j => congrFun (congrArg Subtype.val this) j
  have hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec →
        IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec := by
    intro x hx
    obtain ⟨p₀, hp₀⟩ := (hE.onto x).1 hx
    obtain ⟨w, hw⟩ := hE.frame p₀
    obtain ⟨θ, hθ⟩ := hE.lift p₀
    obtain ⟨Φ, hΦ⟩ := ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1
    refine ⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have hPhi := (hΦ s (Φ s)).2 rfl
    have h₁ := hE.act p₀ w θ s (Φ s) hw hθ hPhi
    have h₂ := hE'.act p₀ w θ s (Φ s) hw hθ hPhi
    have e₁ : v' = mkE E hE (Φ s) := huniq θ _ _ _ hvv h₁
    rw [e₁, hTe, hTe]
    exact h₂
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT
  have hpos : 0 < Module.finrank F (EA A p N) := by
    rw [GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]; positivity
  have : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : EA A p N)
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have h0 : mkE E' hE' s = mkE E' hE' 0 := by rw [← hTe, hc, zero_smul, map_zero]
    have := (hbij E' hE').1 h0
    subst this
    exact hv (map_zero _)
  refine ⟨Units.mk0 c hc0, fun s j => ?_⟩
  have h := congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))
  exact h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferByScaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.eqv_eq_smul | exact GlobalTheory.Mum.eqv_eq_smul | (intros; apply GlobalTheory.Mum.eqv_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpByPull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.GenPull

theorem lbIso_gen_pull : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' gm ψ hψ H
  have e0 : LBIso A'.L (A'.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id A'.isLB
  have hc : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have e1 : LBIso ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) (A'.L.pull (𝟙 _)) := by
    have := GlobalTheory.SiegelPullComp.iso_pull_pull A'.isLB U'.gen.hom.left U'.gen.inv.left
    rwa [hc] at this
  have e2 := GlobalTheory.SiegelPullComp.iso_pull U'.gen.inv.left U'.ext
  have e3 := GlobalTheory.SiegelPullComp.iso_pull_pull U'.LG.isLB (pullback.fst G'.hom (jK R)) U'.gen.inv.left
  have e4 := GlobalTheory.SiegelPullComp.iso_pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) H
  have e5 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB gm (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))
  have hq : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm = ψ ≫ FinalForm.φ := by
    rw [Category.assoc, hψ]
  rw [hq] at e5
  have e6 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB FinalForm.φ ψ
  have e7 := GlobalTheory.SiegelPullComp.iso_pull ψ (⟨FinalForm.w, FinalForm.w_gen⟩ : LBIso _ _)
  have e8 := GlobalTheory.SiegelPullComp.iso_pull_pull ρ.P.isLB (pullback.fst ρ.P.A.hom FinalForm.u₀) ψ
  have hA := A'.isLB
  have hG := U'.LG.isLB
  have hZ := FinalForm.L.isLB
  have hP := ρ.P.isLB
  refine LBIso.trans hA (pull_isLB (pull_isLB hA _) _) (pull_isLB hP _) (LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) e0 e1.symm) ?_
  refine LBIso.trans (pull_isLB (pull_isLB hA _) _) (pull_isLB (pull_isLB hG _) _) (pull_isLB hP _) e2 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hG _) _) (pull_isLB hG _) (pull_isLB hP _) e3 ?_
  refine LBIso.trans (pull_isLB hG _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e4 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) (pull_isLB hP _) e5 ?_
  refine LBIso.trans (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e6.symm ?_
  exact LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e7 e8

end GlobalTheory.Poinc.GenPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  first | exact @GlobalTheory.Poinc.GenPull.lbIso_gen_pull | exact GlobalTheory.Poinc.GenPull.lbIso_gen_pull | (intros; apply GlobalTheory.Poinc.GenPull.lbIso_gen_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section
namespace GlobalTheory.GenPb

theorem genfib_grpPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' ξ gm hgm ξ₀ hξ
  have := U'.gen_hom
  have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
  have gpA : IsGrpPullback A'.A G' (jK R) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) :=
    ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK R))).congr
      (Category.id_comp _) rfl
  have h2 : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ U₀.ι) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm) :=
    (gpA.comp hgm).congr hξ.symm rfl
  have hw : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) ≫ FinalForm.G.hom = (A'.A.hom ≫ ξ₀) ≫ U₀.ι := by
    have := h2.1.w
    simpa [Category.assoc] using this
  refine ⟨FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw,
    FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _, ?_⟩
  have h3 : IsGrpPullback A'.A ((Over.pullback FinalForm.u₀).obj ρ.P.A) ξ₀
      (FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw) :=
    IsGrpPullback.cancel FinalForm.cart (h2.congr rfl (by rw [FinalForm.cart.1.lift_fst, Category.assoc]))
      (FinalForm.cart.1.lift_snd _ _ _)
  exact h3.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)

end GlobalTheory.GenPb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  first | exact @GlobalTheory.GenPb.genfib_grpPullback | exact GlobalTheory.GenPb.genfib_grpPullback | (intros; apply GlobalTheory.GenPb.genfib_grpPullback <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullAlong

theorem sharpBy_pull {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (t : T' ⟶ T) (v : T' ⟶ F.X) (hv : t ≫ u = v)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) (φA : P'.A.left ⟶ P.A.left)
    (hS : SharpBy F W P u c pr) (hA : IsGrpPullback P'.A P.A t φA) (hL : LBIso P'.L (P.L.pull φA)) :
    ∃ (c' : SiegPre g n ζ (v ≫ F.s)) (pr' : Fin 8 → (P'.A ⟶ c'.A)) (χ : c'.A.left ⟶ c.A.left),
      SharpBy F W P' v c' pr' ∧ IsGrpPullback c'.A c.A t χ ∧ ∀ a, (pr' a).left ≫ χ = φA ≫ (pr a).left := by
  subst hv
  obtain ⟨hpb, hmon, huniv, hLc⟩ := hS
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) T T' (u ≫ F.s)
    ((t ≫ u) ≫ F.s) t rfl (by rw [hid, Category.comp_id, Category.assoc])).1 c
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpb hc'
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.T.eighthPowerProjections_groupPullback pr hA hχ hmon huniv
  exact ⟨c', pr', χ, ⟨hcomp, hmon', huniv', GlobalTheory.T.lineBundleIso_eighthPower_groupPullback c.P c'.P P.L P'.L pr pr' W c.isLB c'.isLB P.isLB P'.isLB hsq hP hpr' hL hLc⟩,
    hχ, hpr'⟩

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ FinalForm.u₀ ≫ u) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ S ρ u c pr hS M U₀ EE FinalForm R _ _ _ _ G' _ _ _ D' A' U' ξ gm hgm hLB ξ₀ hξ₀
  obtain ⟨ψ, hψφ, hψs, hψpb⟩ := GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback FinalForm U' ξ gm hgm ξ₀ hξ₀
  have hL := GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback FinalForm U' gm ψ hψφ hLB
  obtain ⟨c', pr', χ, hS', hχ, hpr'⟩ := sharpBy_pull F W ρ.P A' u (ξ₀ ≫ FinalForm.u₀) (ξ₀ ≫ FinalForm.u₀ ≫ u)
    (Category.assoc _ _ _) c pr (ψ ≫ pullback.fst _ _) hS hψpb hL
  refine ⟨c', pr', hS', fun a b f f' hf hff' => ?_⟩
  obtain ⟨-, f₁, hf₁, hf₁φ⟩ := hf
  refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, ?_, by simp⟩
  refine GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport pr pr' a b f₁ _ hψpb hχ hpr' ?_ hf₁
  have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
    pullback.lift_fst _ _ _
  have hmapf₁ : ((Over.pullback FinalForm.u₀).map f₁).left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f₁.left :=
    pullback.lift_fst _ _ _
  have key : (U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom).left ≫ ψ = ψ ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply FinalForm.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hψφ, reassoc_of% hgi, reassoc_of% hmapf, hff', hf₁φ, reassoc_of% hψφ]
    · have w1 : ((Over.pullback FinalForm.u₀).map f₁).left ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom =
          ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom := Over.w _
      have w2 : ψ ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom = A'.A.hom ≫ ξ₀ := hψs
      simp only [Category.assoc, w1, w2]
      rw [← Category.assoc, Over.w]
  rw [← Category.assoc, key, Category.assoc, hmapf₁, Category.assoc]

end GlobalTheory.Poinc.Eq8.PullAlong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndUOfOLinear
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.UT.OLinEnd

noncomputable section

namespace GlobalTheory.Mum.EFix

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem exists_gtPtAct (hG : GlobalFnsSt) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ q : QkPt D F k, q.y = a • p.y ∧ GtPtAct oa a p.g q.g := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, rfl, hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ

end Pts

section End
variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem endU_of_oLinear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtPtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end End

end GlobalTheory.Mum.EFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.GaussBC

theorem two_le_coheight_of_chain {X : Scheme.{0}} {x e g : X} (h₁ : e ⤳ x) (h₂ : g ⤳ e) (n₁ : e ≠ x)
    (n₂ : g ≠ e) : (2 : ℕ∞) ≤ Order.coheight x := by
  have l₁ : x < e := lt_of_le_not_ge h₁ (fun h => n₁ (h₁.antisymm h).eq)
  have l₂ : e < g := lt_of_le_not_ge h₂ (fun h => n₂ (h₂.antisymm h).eq)
  have a₁ := Order.coheight_add_one_le l₁
  have a₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight g + 1 + 1 := by gcongr; exact zero_le
    _ ≤ Order.coheight e + 1 := by gcongr
    _ ≤ Order.coheight x := a₁

theorem not_two_le_coheight_of_ringKrullDim_eq_one {X : Scheme.{0}} (x : X)
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : ¬ (2 : ℕ∞) ≤ Order.coheight x := by
  intro h₂
  rw [ringKrullDim_stalk_eq_coheight] at h
  have : Order.coheight x = 1 := by exact_mod_cast h
  rw [this] at h₂
  exact absurd h₂ (by decide)

theorem apply_genericPoint_ne_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp R) [Flat f] : f (genericPoint X) ≠ closedPoint R := by
  intro h
  let p₀ : Sp R := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : p₀ ⤳ f (genericPoint X) := by
    rw [h]; exact (PrimeSpectrum.le_iff_specializes p₀ (closedPoint R)).mp bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hs
  have hw' : w = genericPoint X := (hw.antisymm (genericPoint_specializes w)).eq
  rw [hw', h] at hfw
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal hfw)

theorem apply_eq_of_closedFibre_dim_one : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hG hpb _ y y' hy hy' hdy hdy'
  haveI : Smooth H.hom := hG.smooth
  haveI : Flat H'.hom := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat H.hom))
  haveI : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ha
  haveI : Flat π := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat (spMap a)))
  have hsq : ∀ z, H.hom (π z) = spMap a (H'.hom z) := fun z => by
    have := congrArg (fun f => f.base z) hpb.w
    simpa using this
  have hcl : spMap a (closedPoint D) = closedPoint T := by
    apply PrimeSpectrum.ext
    show Ideal.comap a (maximalIdeal D) = maximalIdeal T
    have hle : maximalIdeal T ≤ Ideal.comap a (maximalIdeal D) := Ideal.map_le_iff_le_comap.mp hm.le
    exact ((maximalIdeal.isMaximal T).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hback : ∀ p : Sp D, spMap a p = closedPoint T → p = closedPoint D := by
    intro p hp
    by_contra hne
    have hbot : p.asIdeal = ⊥ := by
      by_contra hb
      exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hb)))
    have hker : Ideal.comap a ⊥ = maximalIdeal T := by
      rw [← hbot]; exact congrArg PrimeSpectrum.asIdeal hp
    apply IsDiscreteValuationRing.not_a_field D
    rw [← hm, ← hker]
    exact le_antisymm Ideal.map_comap_le bot_le
  set F : Set H.left := H.hom ⁻¹' {closedPoint T} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint T).preimage H.hom.continuous
  have hFi : IsIrreducible F := by
    haveI := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ H hG _ ((Sp T).fromSpecResidueField (closedPoint T))
    haveI : IrreducibleSpace (H.hom.fiber (closedPoint T)) := this
    have hr := (IrreducibleSpace.isIrreducible_univ (H.hom.fiber (closedPoint T))).image _
      (Scheme.Hom.fiberι H.hom (closedPoint T)).continuous.continuousOn
    rw [Set.image_univ] at hr
    convert hr using 1
    exact (Scheme.Hom.range_fiberι H.hom (closedPoint T)).symm
  have hξ₀ := hFi.isGenericPoint_genericPoint_closure
  rw [hFc.closure_eq] at hξ₀
  set ξ₀ := hFi.genericPoint
  have hgH := apply_genericPoint_ne_closedPoint H.hom
  have hgH' := apply_genericPoint_ne_closedPoint H'.hom
  have hyξ₀ : y = ξ₀ := by
    by_contra hne
    refine not_two_le_coheight_of_ringKrullDim_eq_one y hdy
      (two_le_coheight_of_chain (hξ₀.specializes hy) (genericPoint_specializes ξ₀) (Ne.symm hne) ?_)
    intro h; apply hgH; rw [h]; exact hξ₀.mem
  have hzξ₀ : π y' = ξ₀ := by
    by_contra hne
    have hz : π y' ∈ F := by
      show H.hom (π y') = closedPoint T
      rw [hsq, hy', hcl]
    obtain ⟨w, hw, hπw⟩ := Flat.generalizingMap π (hξ₀.specializes hz)
    refine not_two_le_coheight_of_ringKrullDim_eq_one y' hdy'
      (two_le_coheight_of_chain hw (genericPoint_specializes w) ?_ ?_)
    · rintro rfl; exact hne hπw
    · intro h; apply hgH'; apply hback; rw [← hsq, h, hπw]; exact hξ₀.mem
  rw [hzξ₀, hyξ₀]

end GlobalTheory.Desc.GaussBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  first | exact @GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | exact GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | (intros; apply GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one <;> assumption)
end
end

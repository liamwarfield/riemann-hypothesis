module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ModuleStructureOfCommuting
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.SplitW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.PointRepUnramifiedAtAuxiliaryPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AbsH
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.MapOfRel
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

theorem UpperTheory.V.Hi.JEx.map_of_rel {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T]
    [IsCO O T] (φ : Λ.Λ →ₐ[O] T) (D : GDet n T F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Tˣ) (hc : D.IsCont (maximalIdeal T))
    (hred : D.map (res O T : T →+* ResidueField O) = r.Dbar)
    (hpsi : ∀ v i, r.IsPsi v i (ψ v i) ∧ pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (F.Iv v).subtype)
    (hrel : (∀ i g, D.lam i (F.star O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
      (∀ v (g : Fin n → F.Gv v) (h : F.G₀), D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g) = 0) ∧
      ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0) :
    ∃ f : B.B →ₐ[O] T, B.u.D.map f.toRingHom = D ∧ (∀ v i, pushCh f.toRingHom (B.u.ψ v i) = ψ v i) ∧
      ∀ b, f (Λ.toPair B.u b) = φ b := by
  let p : Pair r T := ⟨D, ψ, hc, hred, fun v i => (hpsi v i).1, hrel.1, hrel.2.1, hrel.2.2⟩
  obtain ⟨f, hf, -⟩ := B.univ T p
  refine ⟨f, hf.1, hf.2, ?_⟩
  let κ' : ∀ v, Fin n → F.Iv v →* Tˣ := fun v i => (ψ v i).comp (F.Iv v).subtype
  have hin : IsInert r κ' := fun v i => ⟨ψ v i, (hpsi v i).1, rfl⟩
  obtain ⟨g, -, hu⟩ := Λ.univ T κ' hin
  have h1 : ∀ v i, pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := by
    intro v i
    have e1 := LamObj.toPair_spec r Λ B.u v i
    have e2 := hf.2 v i
    calc pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i)
        = pushCh (f : B.B →+* T) (pushCh ((Λ.toPair B.u : Λ.Λ →ₐ[O] B.B) : Λ.Λ →+* B.B) (Λ.κ v i)) := by
          ext s
          rfl
      _ = pushCh (f : B.B →+* T) ((B.u.ψ v i).comp (F.Iv v).subtype) := by rw [e1]
      _ = (pushCh (f : B.B →+* T) (B.u.ψ v i)).comp (F.Iv v).subtype := by
          ext s
          rfl
      _ = κ' v i := by rw [e2]
  have h2 : ∀ v i, pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := fun v i => (hpsi v i).2
  have heq := (hu _ h1).trans (hu _ h2).symm
  intro b
  exact DFunLike.congr_fun heq b
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DeformationRingToHeckeAlgebraSurjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.deformationRing_to_heckeAlgebra_surjective :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A T B : Type) [CommRing A] [CommRing T] [Algebra c.O T] [Algebra A T] [CommRing B] [Algebra c.O B] (gen : H.Op → T) (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ) (f : B →ₐ[c.O] T),
    (∀ (w : H.Wp) (P : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver P w.1 → IsFrob P (normV w.1) σ →
      (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    (∀ v (j : Fin n) (x : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (x : G L Ω) → H.art v x = unif _ →
      ((∏ i with i ≤ j, W.pushCh f.toRingHom (ψ₀ v i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ j : A → B, (∀ b, f (j b) = algebraMap A T b) → Algebra.adjoin A (Set.range gen) = ⊤ → Function.Surjective f := by
  intro L Ω _ _ _ _ _ l _ n c H hH A T B _ _ _ _ _ _ gen D₀ ψ₀ f h1 h2 j hj htop
  have hgen : ∀ i, gen i ∈ f.range := by
    rintro (⟨w, k⟩ | ⟨v, k⟩)
    · obtain ⟨P, hP⟩ := exists_isPlaceOver Ω w.1
      obtain ⟨σ, hσ⟩ := exists_isFrob hP
      have hq : IsUnit ((normV w.1 : ℕ) : c.O) := by
        have h0 := (cycZ L Ω l σ).isUnit.map (algebraMap ℤ_[l] c.O)
        rwa [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hP hσ, map_natCast] at h0
      obtain ⟨u, hu⟩ := hq.exists_left_inv
      have huT : algebraMap c.O T u * ((normV w.1 : ℕ) : T) = 1 := by
        rw [← map_natCast (algebraMap c.O T), ← map_mul, hu, map_one]
      have e := JEx.heckePol_coeff n (normV w.1)
        (fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) (k + 1) k.2
      rw [← h1 w P σ hP hσ, dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at e
      have e2 : (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          (D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).map f.toRingHom := by
        let y := MonoidAlgebra.single (H.prj σ⁻¹) (1 : B)
        have he (z : MonoidAlgebra B H.Gq) : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C
            (MonoidAlgebra.mapRingHom H.Gq f.toRingHom z) =
            MonoidAlgebra.mapRingHom H.Gq (Polynomial.mapRingHom f.toRingHom)
              (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C z) := by
          rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
            ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
            ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
        let : Algebra B T[X] := ((algebraMap T T[X]).comp f.toRingHom).toAlgebra
        have hn := D₀.nat B[X] T[X]
          { toRingHom := Polynomial.mapRingHom f.toRingHom
            commutes' := fun a => by change (Polynomial.mapRingHom f.toRingHom) (C a) = C (f a); simp }
          (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C y)
        change (D₀.map f.toRingHom).D T[X] _ = _
        rw [← show MonoidAlgebra.mapRingHom H.Gq f.toRingHom y =
          MonoidAlgebra.single (H.prj σ⁻¹) 1 by simp [y], he y]
        exact hn
      rw [e2, coeff_map] at e
      have e3 : gen (.inl (w, k)) = algebraMap c.O T u ^ ((k + 1) * (k + 1 - 1) / 2 : ℕ) *
          ((-1) ^ ((k : ℕ) + 1) * f ((D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).coeff (n - (k + 1)))) := by
        refine Eq.trans ?_ (congrArg _ e.symm)
        rw [← mul_assoc, ← mul_pow, huT, one_pow, one_mul]
        rfl
      rw [e3]
      exact mul_mem (pow_mem (f.range.algebraMap_mem u) _)
        (mul_mem (pow_mem (neg_mem (one_mem _)) _) (f.mem_range_self _))
    · obtain ⟨y, hy⟩ := (hH.art_spec v).surj (unif _)
      rw [← h2 v k y (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) y) rfl hy, Units.coe_prod]
      refine prod_mem fun i _ => ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      exact mul_mem (f.mem_range_self _) (pow_mem (f.range.algebraMap_mem _) _)
  intro t
  have ht : t ∈ Algebra.adjoin A (Set.range gen) := htop ▸ Algebra.mem_top
  change t ∈ f.range
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | algebraMap r => exact ⟨j r, hj r⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

set_option maxHeartbeats 1000000 in
private theorem absH (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ)
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (hAut : H.Aut ι P)
    (lam : Wt L l n) (hl : lam ∈ H.admitted) (hd : H.DenseWt θ lam) (a : H.Op → c.O) (K : H.Lev)
    {B : Type} [CommRing B] [Algebra c.O B] (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ)
    (j : A →ₐ[c.O] B)
    (key : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : A →ₐ[c.O] T) (gen : H.Op → T),
      (∀ i, gen i - algebraMap c.O T (a i) ∈ maximalIdeal T) →
      ∀ (D : W.GDet n T H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Tˣ), D.IsCont (maximalIdeal T) →
      (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
      (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
        D.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
      (∀ v i (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) * φ (θ (eV n H.Sl v i y)) = 1) →
      (∀ v (j : Fin n) (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ((∏ i with i ≤ j, ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
      ∀ Gd : (T →ₐ[c.O] Qbar l) → Prop, (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
      (∀ x, Gd x → ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), P lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧
        ∀ v, W.HasFlag (ρ.comp (H.dec v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
      ∃ f : B →ₐ[c.O] T, D₀.map f.toRingHom = D ∧ (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = ψ v i) ∧ ∀ b, f (j b) = φ b) :
    ∃ J : Ideal B, H.IsJ θ a K D₀ ψ₀ j J := by
  by_cases hne : H.MK θ a K = ⊥
  · exact ⟨⊤, Or.inl ⟨hne, rfl⟩⟩
  haveI hF : Fact (CommOn (H.MK θ a K) (H.op A)) := ⟨((hiComm L Ω l n c _ hA A θ hθ K).2.2.2 a).1⟩
  obtain ⟨hCO, -, -, hres, -, hgen⟩ := hiAlg L Ω l n c _ hA A θ hθ a K hne
  obtain ⟨D, ψ, hU⟩ := coreDet hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K
  have hO := coreH hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K D ψ hU
  obtain ⟨f, h1, h2, h3⟩ := key (H.TK θ a K) (IsScalarTower.toAlgHom c.O A _) (H.gen θ a K) hres D ψ hU.cont hU.ψ_cont
    hU.frob hU.ψ_unit hU.ψ_unif (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam) (hO.sep lam hl hd)
    fun x hx => by
      obtain ⟨ρ, -, -, e1, e2, e3⟩ := hO.pt lam hl x hx.2.1
      exact ⟨ρ, e1, e2, fun v => (e3 hx v).1⟩
  have h2' : (fun v i => W.pushCh f.toRingHom (ψ₀ v i)) = ψ := funext fun v => funext fun i => h2 v i
  have hU' : H.IsMap θ a K D₀ ψ₀ f := by
    unfold HSet.IsMap
    rw [h1, h2']
    exact hU
  exact ⟨RingHom.ker f, Or.inr ⟨hF, hCO, f, hne, hU',
    deformationRing_to_heckeAlgebra_surjective L Ω l n c _ hA A _ B (H.gen θ a K) D₀ ψ₀ f hU'.frob hU'.ψ_unif _ h3 hgen, h3, rfl⟩⟩

theorem UpperTheory.V.Hi.jEx :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), ∃ J : Ideal B.B, R.IsJ B K J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K
  have hN : GlobalTheory.Mem.LiteralAutomorphy.LitN := hP.litN
  have hA : (hset Q R.τ₀).Ax := axU hN l L Ω s n hn V Q c R.m R.τ₀
  have hAut := autU hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hd : (hset Q R.τ₀).DenseWt R.θ lam := (denseU hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  refine absH hN (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι _ hAut lam (Set.mem_univ _) hd R.a K B.u.D B.u.ψ (Λ.toPair B.u) ?_
  intro T _ _ _ φ gen hres D ψ hc hψ hfr hun huf Gd hsep hpt
  exact JEx.map_of_rel B Λ φ D ψ hc (heckeDeterminant_reduction_eq_residual l L Ω s n V Q c r ι Λ R hA T gen hres D hc hfr)
    (exists_ordinaryCharacters_heckeAlgebra l L Ω s n V Q c r ι Λ R hA T φ gen hres ψ hψ hun huf)
    (heckeDeterminant_satisfies_deformation_relations l L Ω s n hn V c r ι lam T D ψ Gd hsep hpt)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LocEq
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem le_mem_under {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
  rw [map_natCast]

private theorem le_cmp_same {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w w' : Plc L}
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (g : Ga l L n)
    (hg : cmp n w g ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' g ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases h' : ((l : ℕ) : 𝓞 L) ∉ w'.asIdeal
  · have h0 : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
      rw [le_mem_under, ← h, ← le_mem_under]
      exact h'
    obtain ⟨_, x, rfl⟩ := g
    unfold CaseU.cmp at hg ⊢
    rw [dite_eq_left h0] at hg
    rw [dite_eq_left h']
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x w w' h hg
  · unfold CaseU.cmp
    rw [dite_eq_right h']
    exact one_mem _

theorem UpperTheory.V.Hi.levelUR2LevEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ u : Ub n s, u ∈ (hset Q τ₀).lev K ↔ u ∈ (hset Q₀ τ₀).lev K₀ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ K₀ K h0 hK u
  have hem : ∀ q : Q₀.Q, False := fun q => by
    refine Q₀.notS q ?_
    rw [← h0, Q₀.range]
    exact Or.inr ⟨q, rfl⟩
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := levelUR2LevOut l L Ω s n hn V Q c m τ₀ K u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u (fun w hw => ?_) fun q => (hem q).elim
    by_cases hw' : w.under (𝓞 (Lp L)) ∈ V.S'
    · rw [Q.range] at hw'
      rcases hw' with hw' | ⟨q, hq⟩
      · exact (hw (h0 ▸ hw')).elim
      · refine le_cmp_same (w := Q.wq q) hq.symm _ ?_
        have h3 := h2 q
        rw [hK q] at h3
        exact h3
    · exact h1 w hw'
  · intro hu
    obtain ⟨h1, _⟩ := levelUR2LevOut l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K u (fun w hw => h1 w fun hw' => hw ?_) fun q => ?_
    · rw [Q.range]
      exact Or.inl (h0 ▸ hw')
    · rw [hK q]
      exact h1 _ (h0 ▸ Q.notS q)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem lq_lc {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid F O n) : IsLocallyConstant fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1) := by
  have h : IsLocallyConstant fun (g : F.G₀) (i : Fin n) => r.chib i g :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      have := Filter.eventually_all.2 fun i => (JEx.lc_of_open _ (r.chib_open i)).eventually_eq x
      exact this.mono fun y hy => funext hy
  have e : (fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) =
      (fun t : Fin n → (ResidueField O)ˣ => (Matrix.diagonal fun i => (t i : ResidueField O)).charpoly) ∘
        fun (g : F.G₀) (i : Fin n) => r.chib i g := by
    funext g
    rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
    rfl
  rw [e]
  exact h.comp _

private theorem lq_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hc : Continuous p)
    (hs : Function.Surjective p) {S : Set X} (hS : Dense S) {T : Set Y} (h : ∀ x ∈ S, p x ∈ T) : Dense T :=
  (hs.denseRange.dense_image hc hS).mono (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem UpperTheory.V.Hi.levelUR2LocEq :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (r : Resid V₀.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q₀ ι Λ) (K₀ : (hset Q₀ R.τ₀).Lev) (K : (hset Q R.τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q R.τ₀).Op → (hset Q₀ R.τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q R.τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → (∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i)) ∧ ∀ f : (hset Q₀ R.τ₀).X.Fn Λ.Λ R.m, f ∈ (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K ↔ f ∈ (hset Q₀ R.τ₀).MK R.θ R.a K₀ := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c r ι Λ R K₀ K h0 hK p hp hs hpr j hj1 hj2
  have hop : ∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i) := by
    rintro (⟨w, k⟩ | x)
    · obtain ⟨hw, e⟩ := hj2 w k
      exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) e).symm
    · exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) (hj1 x)).symm
  refine ⟨hop, fun f => ?_⟩
  have hAx := axU hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀
  have hAx' := axU hP.litN l L Ω s n hn V Q c _ R.τ₀
  obtain ⟨hdom, hden⟩ := denseU hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀ r Λ R.θ R.theta
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have haut := autU hP l L Ω s n hn V₀ Q₀ c r ι _ R.τ₀ R.type
  have hlev : (hset Q R.τ₀).lev K = (hset Q₀ R.τ₀).lev K₀ :=
    Subgroup.ext fun u => levelUR2LevEq l L Ω s n hn V₀ V Q₀ Q c _ R.τ₀ K₀ K h0 hK u
  have key := levelUR2H3Abs hP.litN L Ω l n c _ hAx Λ.Λ R.θ R.isWt hdom ι _ haut lam trivial (hden lam) R.a K₀
    _ (lq_lc r) R.res.frob _ j (fun x => ⟨.inr x, hj1 x⟩) (lq_dense hp hs hAx'.dense (by
      rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      obtain ⟨hw0, -⟩ := hj2 ⟨w, hw⟩ ⟨0, hn⟩
      refine ⟨⟨w, hw0⟩, fun k => ?_, B, σ, hB, hσ, hpr _⟩
      obtain ⟨_, e⟩ := hj2 ⟨w, hw⟩ k
      exact ⟨_, e⟩))
  rw [← key]
  have e1 : (hset Q R.τ₀).op Λ.Λ = fun i => (hset Q₀ R.τ₀).op Λ.Λ (j i) := funext hop
  have e2 : (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K = _ :=
    congrArg₂ (fun U o => locPart ((hset Q₀ R.τ₀).X.Ord ((hset Q₀ R.τ₀).τA Λ.Λ) R.θ U) o
      fun i => algebraMap c.O Λ.Λ (R.a (j i))) hlev e1
  exact SetLike.ext_iff.1 e2 f
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UpU
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.upU :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ∀ (x : B.Pt) (h : s.Wt n) (lam : Wt L l n), x.Arith h → WtOf h lam → ∀ (σ : Submodule ℂ (UA L n → ℂ)) (ρ : G L Ω →* GL (Fin n) (Qbar l)), IsAutRepU σ → Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ → x.IsRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι ρ w τ) → (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → (∀ v : V.frame.Vl, ∃ (τ : SmIrr (GLw n (s.w v.1))) (ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i)) → J ≤ RingHom.ker x := by
  exact UpperTheory.V.Hi.Up.main
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

open Formalism.MainNotions.N

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}

end SlopeTestRemainingChoices

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JrTeichEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KillsStar
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Gcomm
open Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.AlgebraTools.Det.gcomm :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G),
    (∀ (B : Type) [CommRing B] [Algebra A B] (x y : MonoidAlgebra B G), D.D B (1 + x * y) = D.D B (1 + y * x)) ∧
    ∃ I : TwoSidedIdeal (MonoidAlgebra A G), ∀ y, y ∈ I ↔ D.Kills y := by
  intro n A G _ _ D
  refine ⟨fun B _ _ x y => ?_, D.toDet.ker, fun y =>
    (UpperTheory.V.CA.d_ker D.toDet y).1.trans (UpperTheory.V.CA.d_toDet D y).2.2.2⟩
  have h := UpperTheory.V.CA.d_comm D.toDet B (toT A G B x) (toT A G B y)
  change D.D B (ofT A G B _) = D.D B (ofT A G B _) at h
  simpa only [map_add (f := _), map_one, map_mul, ofT_toT] using h
end

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsStar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D → ∀ y, D.Kills y → D.Kills (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n D hP y hy B _ _ h
  letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨-, -, -, -, -, snat⟩ := AlgebraTools.Det.starApi F O R n
  obtain ⟨bmul, b1, badd, -, binv, -⟩ := AlgebraTools.Det.starApi F O B n
  have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) (F.star O R n y)
      = F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y) :=
    (snat B (IsScalarTower.toAlgHom O R B) y).symm
  rw [hm]
  have key : 1 + h * F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y)
      = F.star O B n (1 + MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y * F.star O B n h) := by
    rw [badd, bmul, b1, binv]
  rw [key, hP B, (AlgebraTools.Det.gcomm D).1 B]
  exact hy B (F.star O B n h)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Abstract

open UpperTheory.V.W

end Abstract
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JDense
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

end

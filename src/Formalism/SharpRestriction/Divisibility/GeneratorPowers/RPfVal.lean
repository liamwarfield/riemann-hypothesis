module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Pj.Crude Formalism.MainNotions.ModuliIntegralCharts.H1

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem vLa_int_not_mem {a : 𝓞 K} (ha : a ∉ la.asIdeal) : vLa la (a : K) = 0 := by
  have h : (a : K) = algebraMap (𝓞 K) K a := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 ha]
  simp

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hl := resCharOf_prime la
    have hnd : ¬ resCharOf la ∣ p := fun hd =>
      hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

theorem padic_prime (l : ℕ) [Fact l.Prime] {p : ℕ} (hp : p.Prime) :
    padicValNat l p = if l = p then 1 else 0 := by
  rw [Nat.padicValNat_def]
  split_ifs with h
  · subst h; exact Nat.multiplicity_self hp.one_lt
  · have : Fact p.Prime := ⟨hp⟩
    exact multiplicity_primes h

theorem vLa_pPow {Q q d : ℕ} (hQ : Q ≠ 0) (hq : q.Prime) (hd : d.Prime) (a b c : ℕ) :
    vLa la (((Q ^ a * q ^ b * d ^ c : ℕ) : ℕ) : K) =
      (((a * padicValNat (resCharOf la) Q + b * (if resCharOf la = q then 1 else 0) +
        c * (if resCharOf la = d then 1 else 0)) * ramOverZ la : ℕ) : ℤ) := by
  have hl := resCharOf_prime la
  have : Fact (resCharOf la).Prime := ⟨hl⟩
  have h2 : (Q ^ a : ℕ) ≠ 0 := pow_ne_zero _ hQ
  have hq' : (q ^ b : ℕ) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hd' : (d ^ c : ℕ) ≠ 0 := pow_ne_zero _ hd.ne_zero
  rw [crv_vLa_natCast la (Nat.mul_ne_zero (Nat.mul_ne_zero h2 hq') hd')]
  congr 2
  have e1 : padicValNat (resCharOf la) (Q ^ a) = a * padicValNat (resCharOf la) Q := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  have e2 : padicValNat (resCharOf la) (q ^ b) = b * padicValNat (resCharOf la) q := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  have e3 : padicValNat (resCharOf la) (d ^ c) = c * padicValNat (resCharOf la) d := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero h2 hq') hd', (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h2 hq', e1, e2, e3,
    padic_prime _ hq, padic_prime _ hd]

theorem nat_mem_iff (n : ℕ) : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la ∣ n := by
  constructor
  · intro hm
    by_contra hnd
    exact crv_not_mem la hnd hm
  · rintro ⟨k, rfl⟩
    push_cast
    exact la.asIdeal.mul_mem_right _ (crv_char_mem la)

variable {D : D7} {j : ℕ}

theorem piG_mul_bar (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply RingOfIntegers.coe_injective
  have h := EX.piG_norm i
  push_cast
  exact h

theorem nnW_not_mem (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    nnW B hinj EX w ∉ la.asIdeal := by
  have hπ : ∀ i, iE D hinj B (EX.piG i) ∉ la.asIdeal ∧ iE D hinj B (piBarO EX i) ∉ la.asIdeal := by
    intro i
    have hn : iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 B.KO) := by
      rw [← map_mul, piG_mul_bar, map_natCast]
    exact ⟨fun hm => hg i (hn ▸ la.asIdeal.mul_mem_right _ hm),
      fun hm => hg i (hn ▸ la.asIdeal.mul_mem_left _ hm)⟩
  have : nnW B hinj EX w ∈ la.asIdeal.primeCompl := by
    unfold nnW
    exact Submonoid.prod_mem _ fun i _ =>
      Submonoid.mul_mem _ (Submonoid.pow_mem _ (hπ i).1 _) (Submonoid.pow_mem _ (hπ i).2 _)
  exact this

theorem vAdd_sW (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    ((vAdd la (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) : ℤ) : ℝ) =
      (ramOverZ la : ℝ) * clOf w la := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hq2 : D.host.q ≠ 2 := by omega
  have hd2 : D.host.d ≠ 2 := by omega
  have hqd : D.host.q ≠ D.host.d := by omega
  have hnn := nnW_not_mem B hinj EX w la hg
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn ((NumberField.RingOfIntegers.coe_eq_zero_iff.1 h) ▸ la.asIdeal.zero_mem)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN0 : ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) ≠ 0 := by
    rw [hP]
    exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  have hc : (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO _ = _
    rw [map_mul, map_natCast]
  show ((vLa la _ : ℤ) : ℝ) = _
  rw [hc, crv_vLa_mul la hnn0 hN0, vLa_int_not_mem la hnn, hP, vLa_pPow la D.host.QS_pos.ne' hq hd]
  unfold clOf
  rw [show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
  simp only [nat_mem_iff la D.host.QS, prime_mem_iff la hq, prime_mem_iff la hd]
  by_cases hS : resCharOf la ∣ D.host.QS
  · have h1 : resCharOf la ≠ D.host.q := fun h => D.host.q_not_dvd_QS (h ▸ hS)
    have h2 : resCharOf la ≠ D.host.d := fun h => D.host.d_not_dvd_QS (h ▸ hS)
    rw [if_pos hS, if_neg h1, if_neg h2]
    generalize padicValNat (resCharOf la) D.host.QS = m
    push_cast; ring
  · rw [if_neg hS, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hS]
    split_ifs <;> (try (exfalso; omega)) <;> (try (exfalso; tauto)) <;> push_cast <;> ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace H1algLink

open Formalism.L2.Pj.Crude

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem liesOver_resChar : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := resCharOf_prime la
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem span_resChar_ne_bot : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (resCharOf_prime la).ne_zero

theorem eWL_eq : eWL K la = ramOverZ la := by
  have := liesOver_resChar la
  unfold eWL ramOverZ
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (span_resChar_ne_bot la)).symm

theorem ramOverZ_ne_zero : ramOverZ la ≠ 0 := by
  have := liesOver_resChar la
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal (span_resChar_ne_bot la)

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hnd : ¬ resCharOf la ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq (resCharOf_prime la) hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

variable {D : D7}

end H1algLink


end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (overAt x0 (DualNumber S) ⟶ G) where
  carrier := {W | smT x0 0 W = 1}
  mul_mem' {u w} hu hw := by
    have hu : smT x0 0 u = 1 := hu
    have hw : smT x0 0 w = 1 := hw
    show smT x0 0 (u * w) = 1
    rw [smT_mul, hu, hw, _root_.mul_one]
  one_mem' := smT_one' x0 0
  inv_mem' {W} hW := by
    have hW : smT x0 0 W = 1 := hW
    show smT x0 0 W⁻¹ = 1
    have h := map_inv (smHom x0 (G := G) 0) W
    change smT x0 0 W⁻¹ = (smT x0 0 W)⁻¹ at h
    rw [h, hW, inv_one]

abbrev TanM := Additive (tanSub x0 G)

variable {x0 G}

def tv (m : TanM x0 G) : overAt x0 (DualNumber S) ⟶ G := (Additive.toMul m : tanSub x0 G)

theorem tv_zero' (m : TanM x0 G) : smT x0 0 (tv m) = 1 := (Additive.toMul m).2

def mkT (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : TanM x0 G := Additive.ofMul ⟨W, h⟩

theorem tv_injective : Function.Injective (tv (x0 := x0) (G := G)) := fun _ _ h => Subtype.ext h

theorem tv_add (m m' : TanM x0 G) : tv (m + m') = tv m * tv m' := rfl

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x0 G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

instance : Module S (TanM x0 G) where
  smul a m := mkT (smT x0 a (tv m)) (by rw [smT_smT, zero_mul]; exact tv_zero' m)
  one_smul m := tv_injective (smT_unit x0 (tv m))
  mul_smul a b m := tv_injective (smT_smT x0 a b (tv m)).symm
  smul_zero a := tv_injective (smT_one' x0 a)
  smul_add a m m' := tv_injective (smT_mul x0 a (tv m) (tv m'))
  add_smul a b m := tv_injective (smT_add x0 (tv m) (tv_zero' m) a b)
  zero_smul m := tv_injective (tv_zero' m)

def postL (φ : G ⟶ G) [IsMonHom φ] : Module.End S (TanM x0 G) where
  toFun m := mkT (tv m ≫ φ) (by rw [smT_post, tv_zero' m, MonObj.one_comp])
  map_add' m m' := tv_injective (MonObj.mul_comp (tv m) (tv m') φ)
  map_smul' a m := tv_injective (smT_post x0 a (tv m) φ).symm

theorem tv_postL (φ : G ⟶ G) [IsMonHom φ] (m : TanM x0 G) : tv (postL φ m) = tv m ≫ φ := rfl

def actL {O : Type} [CommRing O] (ρ : OAct O G) : O →+* Module.End S (TanM x0 G) where
  toFun a := letI := ρ.hom a; postL (ρ.act a)
  map_one' := LinearMap.ext fun m => tv_injective (by
    rw [tv_postL, ρ.one, Category.comp_id]; rfl)
  map_mul' a b := LinearMap.ext fun m => tv_injective (by
    rw [Module.End.mul_apply, tv_postL, tv_postL, tv_postL, mul_comm a b, ρ.mul, Category.assoc])
  map_zero' := LinearMap.ext fun m => tv_injective (by
    have h0 : ρ.act 0 = 1 := by
      have h := ρ.add 0 0
      rw [add_zero] at h
      have h' : ρ.act 0 * ρ.act 0 = ρ.act 0 * 1 := by rw [_root_.mul_one]; exact h.symm
      exact mul_left_cancel h'
    rw [tv_postL, h0, MonObj.comp_one]; rfl)
  map_add' a b := LinearMap.ext fun m => tv_injective (by
    rw [LinearMap.add_apply, tv_add, tv_postL, tv_postL, tv_postL, ρ.add, MonObj.comp_mul])

theorem tv_comb {κ : Type} [Fintype κ] (v : κ → TanM x0 G) (a : κ → S) :
    tv (∑ k, a k • v k) = ∏ k, smT x0 (a k) (tv (v k)) := by
  rw [tv_sum]; rfl

end Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem frTanBasis_holds (Xo : Moduli Dw l) (c : Coeff l) : FrTanBasisSt Xo c := by
  classical
  intro S _ _ y w hw
  haveI : CharZero S := charZero_of_injective_algebraMap (algebraMap c.F S).injective
  let G := Xo.univ.t.G
  let ρ : 𝓞 E →+* Module.End S (TanM y.x G) := actL Xo.univ.t.act
  let χ : (E →+* ℂ) → (E →+* S) := fun σ => (algebraMap c.F S).comp (embF c σ)
  have hχ : Function.Injective χ := by
    intro σ τ h
    ext x
    have h1 := RingHom.congr_fun h x
    have h2 : embF c σ x = embF c τ x := (algebraMap c.F S).injective h1
    exact congrArg (fun z : c.F => (z : ℂ)) h2
  have hcard : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := by
    convert NumberField.Embeddings.card E ℂ
  let U : Lt1 Dw → TanM y.x G := fun ℓ =>
    mkT (ovT (t := Xo.univ.t) (y.tan ℓ.1 ℓ.2)) (smT_zero_ovT (y.tan ℓ.1 ℓ.2))
  have hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ (a : E) • U ⟨σ, i⟩ := fun σ i a =>
    tv_injective ((isEigAt_iff σ (ovT (t := Xo.univ.t) (y.tan σ i))).1 (y.eig σ i) a)
  have hcombσ : ∀ σ (cf : Fin (Dw.mult σ) → S) (W : TanM y.x G),
      IsCombAt y.x (y.u σ) cf (tv W).left ↔ ∑ i, cf i • U ⟨σ, i⟩ = W := by
    intro σ cf W
    have e := isCombAtG_iff Xo.univ.t y.x (fun j => ovT (t := Xo.univ.t) (y.tan σ j)) cf (tv W).left
    refine e.trans ⟨fun h => tv_injective ?_, fun h => ?_⟩
    · rw [tv_comb]
      exact Over.OverMorphism.ext h
    · rw [← h, tv_comb]
      rfl
  have hb : ∀ σ (W : TanM y.x G), (∀ a : 𝓞 E, ρ a W = χ σ (a : E) • W) →
      ∃! cf : Fin (Dw.mult σ) → S, ∑ i, cf i • U ⟨σ, i⟩ = W := by
    intro σ W hW
    have hT : IsTanAt y.x (tv W).left := isTanAtG_of (t := Xo.univ.t) (tv W) (tv_zero' W)
    have hE : IsEigAt c σ (tv W).left :=
      (isEigAt_iff σ (tv W)).2 fun a => congrArg tv (hW a)
    obtain ⟨cf, hcf, hu⟩ := y.basis σ _ hT hE
    exact ⟨cf, (hcombσ σ cf W).1 hcf, fun cf' h => hu cf' ((hcombσ σ cf' W).2 h)⟩
  let W0 : TanM y.x G := mkT (ovT (t := Xo.univ.t) hw) (smT_zero_ovT hw)
  obtain ⟨a, ha, hu⟩ := FrTanAlg.global_basis χ hχ hcard ρ U hU hb W0
  let e := Fintype.equivFin (Lt1 Dw)
  have hiff : ∀ a' : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u (e.symm i).1 (e.symm i).2) (fun i => a' (e.symm i)) w ↔ ∑ ℓ, a' ℓ • U ℓ = W0 := by
    intro a'
    have e1 := isCombAtG_iff Xo.univ.t y.x (fun i => ovT (t := Xo.univ.t) (y.tan (e.symm i).1 (e.symm i).2))
      (fun i => a' (e.symm i)) w
    have hprod : combT y.x (fun i => ovT (t := Xo.univ.t) (y.tan (e.symm i).1 (e.symm i).2))
        (fun i => a' (e.symm i)) = tv (∑ ℓ, a' ℓ • U ℓ) := by
      rw [tv_comb]
      exact Equiv.prod_comp e.symm (fun ℓ => smT y.x (a' ℓ) (tv (U ℓ)))
    refine e1.trans ⟨fun h => tv_injective ?_, fun h => ?_⟩
    · rw [← hprod]
      exact Over.OverMorphism.ext h
    · rw [hprod, h]
      rfl
  exact ⟨a, (hiff a).2 ha, fun a' h => hu a' ((hiff a').1 h)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan
end
end

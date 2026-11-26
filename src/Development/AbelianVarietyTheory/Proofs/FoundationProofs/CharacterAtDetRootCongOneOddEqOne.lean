module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootCong

theorem map_sigR {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem quot_fixed {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : B →+* B) (x Y : Aˣ) (u y y' : B)
    (hx : f x = u * s (f x)) (hy : y = u * s y) (hyy : y * y' = 1) (hY : f (Y⁻¹ : Aˣ) = y') :
    s ((Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) : B) = (Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) := by
  have hs : s y * s y' = 1 := by rw [← map_mul, hyy, map_one]
  change s (f ((x : A) * (Y⁻¹ : Aˣ))) = f ((x : A) * (Y⁻¹ : Aˣ))
  rw [map_mul, hY, map_mul]
  linear_combination (-y') * hx + (s (f x) * s y' * y') * hy - (s (f x) * s y') * hyy
    + (u * s (f x) * y') * hs

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) :=
  map_sigR _ _ x

theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = 1 ∧ finPart D (Y : AE D) = y ∧
      finPart D ((Y⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h1 : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, mul_one]
    exact map_one e.symm
  refine ⟨⟨e.symm (1, y), e.symm (1, y'), h1, by rw [mul_comm, h1]⟩,
    (he _).1.symm.trans ?_, (he _).2.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem exists_idF (D : D7) (b : (Af D.host.F)ˣ) :
    ∃ a : (AF D.host.F)ˣ, finPart D (idF D a : AE D) =
      algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) b := by
  refine ⟨⟨(1, b), (1, (b⁻¹ : (Af D.host.F)ˣ)), Prod.ext (mul_one _) b.mul_inv,
    Prod.ext (mul_one _) b.inv_mul⟩, ?_⟩
  rfl

theorem char_root_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  intro D V c N hN hF hinf hcong g x hx ⟨w, hw, hwe⟩
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹)) (quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.DetRootCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_detRoot_cong_one_odd_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  first | exact @GlobalTheory.DetRootCong.char_root_eq_one | exact GlobalTheory.DetRootCong.char_root_eq_one | (intros; apply GlobalTheory.DetRootCong.char_root_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemPrime

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem isIntegral_star {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd D.host.E) hx

theorem evalV_algebraMap_mem (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.F) (ht : IsIntegral ℤ t) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) t) ∈ v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes]
  have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) t) = v.valuation D.host.F t :=
    v.valuedAdicCompletion_eq_valuation' _
  show Valued.v (algebraMap D.host.F (Fv D.host.F v) t) ≤ 1
  rw [h2]
  exact v.valuation_le_one (K := D.host.F) (⟨t, ht⟩ : 𝓞 D.host.F)

theorem exists_trace {z : Formalism.L2.Theta.AE D} (hz : z ∈ intL D) :
    ∃ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, z + cA D z = fj D β := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    obtain ⟨t, ht⟩ := exists_of_star_eq D (x := (o : D.host.E) + star (o : D.host.E))
      (by rw [star_add, star_star, add_comm])
    have hti : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ht]
      exact o.2.add (isIntegral_star o.2)
    refine ⟨algebraMap D.host.F (Af D.host.F) t * α, fun v => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (evalV_algebraMap_mem v t hti) (hα v)
    · rw [cA_tmul, ← TensorProduct.tmul_add, ← ht, tmul_algebraMap_eq, fj_eq]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [map_zero, map_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, fun v => by rw [map_add]; exact add_mem (ha v) (hb v), by
      rw [RingHom.map_add (f := _), map_add (fj D), ← h1, ← h2, add_add_add_comm]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, h1⟩ := hx
    exact ⟨-a, fun v => by rw [map_neg]; exact neg_mem (ha v), by
      rw [RingHom.map_neg, map_neg (fj D), ← h1, neg_add]⟩

theorem finPart_mem {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])

theorem mem_iff {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (y : Fv D.host.F v) :
    finPart D (fj D (singleV D.host.F v y) * e) ∈ intAE D ↔ Valued.v y ≤ 1 := by
  constructor
  · intro h
    have h1 := inF_mem h
    rw [inF_finPart, ← mul_assoc, ← map_mul, one_mul] at h1
    obtain ⟨β, hβ, h2⟩ := exists_trace h1
    rw [map_mul, cA_fj, ← mul_add, he.2.2, ← map_mul] at h2
    have h3 := congrArg (evalV D.host.F v) (fj_inj D h2)
    rw [map_mul, evalV_singleV_same, evalV_singleV_same, mul_one] at h3
    rw [h3]
    exact hβ v
  · intro h
    rw [RingHom.map_mul]
    exact mul_mem_int (AddSubgroup.subset_closure
      ⟨singleV D.host.F v y, singleV_mem_intAf D.host.F v ⟨y, h⟩, 1, rfl⟩) (finPart_mem he)

theorem singleV_add (v : HeightOneSpectrum (𝓞 D.host.F)) (x y : Fv D.host.F v) :
    singleV D.host.F v (x + y) = singleV D.host.F v x + singleV D.host.F v y := by
  rw [← sub_eq_iff_eq_add, ← singleV_sub, add_sub_cancel_right]

theorem scalar_eq {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {a b : Fv D.host.F v}
    (h : fj D (singleV D.host.F v a) * e = fj D (singleV D.host.F v b) * e) : a = b := by
  have := he.scalar_inj h
  rwa [evalV_singleV_same, evalV_singleV_same] at this

theorem exists_hom {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) :
    ∃ φ : D.host.E →+* Fv D.host.F v, ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e := by
  choose f hf using fun x => he.exists_scalar (incA D x)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := fun x y => ?_, map_zero' := ?_, map_add' := fun x y => ?_ }, hf⟩
  · refine scalar_eq he ?_
    rw [← hf, map_one, mul_one, he.pl_mul]
  · refine scalar_eq he ?_
    have h : singleV D.host.F v (f x * f y) = singleV D.host.F v (f x) * singleV D.host.F v (f y) := by
      rw [singleV_mul, evalV_singleV_same]
    rw [← hf, map_mul, h, map_mul, ← mul_assoc, hf, mul_assoc, hf, mul_assoc]
  · refine scalar_eq he ?_
    rw [← hf, map_zero, mul_zero, ← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self, map_zero, zero_mul]
  · refine scalar_eq he ?_
    rw [← hf, map_add (f := _), singleV_add, map_add (f := _), mul_add, add_mul, hf, hf]

theorem hom_algebraMap {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {φ : D.host.E →+* Fv D.host.F v}
    (hφ : ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e) (t : D.host.F) :
    φ (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (Fv D.host.F v) t := by
  refine scalar_eq he ?_
  have h1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (algebraMap D.host.F (AF D.host.F) t * 1) :=
    tmul_algebraMap_eq (1 : AF D.host.F) t
  have h2 : evalV D.host.F v (algebraMap D.host.F (AF D.host.F) t * 1).2 * 1 =
      algebraMap D.host.F (Fv D.host.F v) t := by
    rw [mul_one, mul_one]
    exact (evalV D.host.F v).commutes t
  rw [← hφ, h1, ← h2, ← singleV_mul, ← algebraMap_mul_fj, mul_assoc, he.pl_mul, mul_comm]

theorem exists_isIdemAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : Formalism.L2.Theta.AE D), GlobalTheory.IdemModTwo.SplitAt D v e → ∃ PP : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  intro D v e he
  obtain ⟨φ, hφ⟩ := exists_hom he
  have hint : ∀ x : 𝓞 D.host.E, Valued.v (φ x) ≤ 1 := fun x => by
    rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {x | Valued.v (φ x) < 1}
      add_mem' := fun {a b} ha hb => by
        show Valued.v (φ ((a : D.host.E) + b)) < 1
        rw [map_add (f := _)]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        show Valued.v (φ 0) < 1
        rw [map_zero, map_zero]; exact zero_lt_one
      smul_mem' := fun c x hx => by
        show Valued.v (φ ((c : D.host.E) * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hI : ∀ x, x ∈ I ↔ Valued.v (φ x) < 1 := fun x => Iff.rfl
  have hcomap : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
    ext t
    rw [Ideal.mem_comap, hI]
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) := rfl
    have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) (algebraMap (𝓞 D.host.F) D.host.F t)) =
        v.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h1, hom_algebraMap he hφ, h2]
    exact v.valuation_lt_one_iff_mem _
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : 𝓞 D.host.E) ∈ I := by rw [h]; trivial
      have h2 : Valued.v (φ 1) < 1 := h1
      rw [map_one, map_one] at h2
      exact lt_irrefl _ h2
    · have h2 : Valued.v (φ ((a : D.host.E) * b)) < 1 := hab
      rw [map_mul, map_mul] at h2
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h2 (not_lt.2 (one_le_mul hn.1 hn.2))
  have hne : I ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hcomap, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨⟨I, hprime, hne⟩, ⟨(isSplitIdem_iff e).2 ⟨v, he⟩, fun x hx => ?_⟩, hcomap⟩
  have hx0 : Valued.v (φ x) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]
    exact fun h => hx (Subtype.ext h)
  show x ∈ I ↔ _
  rw [hI, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

end GlobalTheory.IdemPrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    ∃ x : E, y - (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    rw [TensorProduct.tmul_add, add_sub_add_comm]
    exact add_mem hx hx'
  | tmul a e =>
    obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he' : IsIntegral ℤ (m • e) := he e (Finset.mem_singleton_self e)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have hcont : Continuous fun z : Fv F v => (m : F)⁻¹ • a - z := continuous_sub_left _
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v).exists_mem_open
      (hO.preimage hcont) ⟨(m : F)⁻¹ • a, by simp⟩
    refine ⟨k • (m • e), ?_⟩
    have hk' : (m : F)⁻¹ • a - algebraMap F (Fv F v) k ∈ v.adicCompletionIntegers F := hk
    have h := tmul_mem_intLoc (E := E) hk' ⟨m • e, he'⟩
    convert h using 1
    change _ = ((m : F)⁻¹ • a - algebraMap F (Fv F v) k) ⊗ₜ[F] (m • e)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul F m e, inv_smul_smul₀ hmF]

theorem isIntegral_of_absBar_le_one (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1) :
    ∃ p : Polynomial (v.valuationSubringAtPrime F), p.Monic ∧
      p.eval₂ ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype) x = 0 := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have h1 : (minpoly F x).map (algebraMap F (FvBar F v)) ∈ Polynomial.lifts (valBar F v).integer.subtype := by
    refine Polynomial.Splits.mem_lift_of_roots_mem_range (IsAlgClosed.splits _) (hmon.map _) _ fun a ha => ?_
    have ha' : a ∈ (minpoly F x).rootSet (FvBar F v) := by
      rw [Polynomial.rootSet_def]; simpa [Polynomial.aroots_def] using ha
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at ha'
    obtain ⟨τ, rfl⟩ := ha'
    exact ⟨⟨τ x, hx τ⟩, rfl⟩
  have h2 : minpoly F x ∈ Polynomial.lifts (v.valuationSubringAtPrime F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have h3 : absBar F v (algebraMap F (FvBar F v) ((minpoly F x).coeff n)) ≤ 1 := by
      rw [← Polynomial.coeff_map, ← hc]; exact c.2
    rw [IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), absBar_algebraMap] at h3
    have h4 : Valued.v (algebraMap F (Fv F v) ((minpoly F x).coeff n)) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h3)
    refine ⟨⟨(minpoly F x).coeff n, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le h4
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic h2 hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq]
  exact minpoly.aeval F x

theorem one_tmul_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1) : (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  let : Algebra (v.valuationSubringAtPrime F) E :=
    ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype).toAlgebra
  have : IsScalarTower (𝓞 F) (v.valuationSubringAtPrime F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (v.valuationSubringAtPrime F) x :=
    isIntegral_of_absBar_le_one v x fun τ => by simpa using (absFin_le_iff F v).1 hx τ
  obtain ⟨⟨s, hs⟩, h2⟩ := IsIntegral.exists_multiple_integral_of_isLocalization v.asIdeal.primeCompl x h1
  have h3 : IsIntegral ℤ ((s : F) • x) := isIntegral_trans _ h2
  have hv : v.valuation F (s : F) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hs0 : (s : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have h := tmul_mem_intLoc (E := E) h4 ⟨_, h3⟩
  convert h using 1
  change _ = (algebraMap F (Fv F v) (s : F)⁻¹) ⊗ₜ[F] ((s : F) • x)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hs0]

theorem mem_intLoc_iff_absFin_le_one {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ absFin F v y ≤ 1 := by
  refine ⟨absFin_le_one_of_mem_intLoc, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v y
  have h1 : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1 := by
    have := absFin_add_le F v y (-(y - (1 : Fv F v) ⊗ₜ[F] x))
    rw [absFin_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    exact this.trans (max_le hy (absFin_le_one_of_mem_intLoc hx))
  simpa using add_mem hx (one_tmul_mem_intLoc v x h1)

theorem algebraMap_basis_repr {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ y * τ (b i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
  | tmul a e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      trace_eq_sum_embeddings, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finEmb_tmul, map_mul]; ring

theorem absFin_eq_zero_iff {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} : absFin F v y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun h => by rw [h, absFin_zero]⟩
  have h0 : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ y = 0 := fun τ =>
    (absBar_eq_zero F v).1 (le_antisymm ((absFin_le_iff F v).1 hy.le τ) zero_le)
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (Fv F v) b.traceDual).ext_elem fun i => ?_
  refine (algebraMap (Fv F v) (FvBar F v)).injective ?_
  rw [algebraMap_basis_repr]
  simp [h0]

end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseIdeleTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem adele_algebraMap_apply (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k := rfl

theorem adele_mul_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a * b) v = a v * b v := rfl

theorem adele_sub_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a - b) v = a v - b v := rfl

theorem adele_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem close_scaled (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : FiniteAdeleRing (𝓞 F) F) (k m : F) (hm : m ≠ 0) (n : ℕ)
    (h : Valued.v (a v - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) * v.valuation F m) :
    Valued.v (f a P - algebraMap E _ (algebraMap F E k)) ≤
      WithZero.exp (-(n : ℤ)) * P.valuation E (algebraMap F E m) := by
  have hm1 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
  have hm2 : P.valuation E (algebraMap F E m) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simpa using hm)
  have h1 := h0 ((a - algebraMap F _ k) * algebraMap F _ m⁻¹) n (by
    rw [adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply, map_mul, val_algebraMap,
      map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm1)).2 h)
  rw [map_mul, map_sub, hf, hf, adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply,
    map_mul, val_algebraMap, map_inv₀, map_inv₀] at h1
  exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm2)).1 h1

theorem val_eq_one (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (h : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    Valued.v (f a P) = 1 := by
  have e1 : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← adele_mul_apply, Units.mul_inv, adele_one_apply, map_one]
  have e2 : Valued.v (f a P) * Valued.v (f (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) P) = 1 := by
    rw [← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]
  rw [h, one_mul] at e1
  have l1 := h0 a 0 (by simp [h])
  have l2 := h0 (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) 0 (by simp [e1])
  simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero] at l1 l2
  refine le_antisymm l1 ?_
  rw [← e2]
  exact mul_le_of_le_one_right' l2

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem algebraMap_tmul_one {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (k : R) : (algebraMap R A k) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B k) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_approx (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : FiniteAdeleRing (𝓞 F) F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (χ : HChar E) (hχ : χ.TrivOn F) (N : ℕ) (hN : 0 < N) (α : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ),
      (∀ P ∈ S, Valued.v (f α P) = P.valuation E (k P : E) ∧
        Valued.v (f α P - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E)) ∧
      (∀ P, P ∉ S → Valued.v (f α P) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) ∧
      ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) = 1 := by
  classical
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx F N hN α
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨S.biUnion (aboveF (L := E) F), fun P => upF F (k (P.under (𝓞 F))), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨v, hv, hPv⟩ := Finset.mem_biUnion.1 hP
    obtain rfl := (mem_aboveF v P).1 hPv
    obtain ⟨-, b1, b2⟩ := hS _ hv
    beta_reduce
    set kk := k (P.under (𝓞 F)) with hkk
    have hk : ((upF F kk : Eˣ) : E) = algebraMap F E kk := rfl
    rw [hk]
    have c1 := close_scaled f hf P _ (h0 P) α kk (N * kk) (mul_ne_zero hNF kk.ne_zero) 0 (by simpa using b1)
    have c2 := close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)
    refine ⟨?_, by simpa using c1⟩
    rw [← val_algebraMap]
    apply Valuation.map_eq_of_sub_lt
    rw [val_algebraMap]
    refine c2.trans_lt ?_
    have hm2 : P.valuation E (algebraMap F E kk) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp)
    refine mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro P hP
    have hv : P.under (𝓞 F) ∉ S := fun h =>
      hP (Finset.mem_biUnion.2 ⟨_, h, (mem_aboveF _ P).2 rfl⟩)
    obtain ⟨b1, b2⟩ := hS' _ hv
    refine ⟨val_eq_one f P _ (h0 P) α b1, fun h => b2 ?_⟩
    change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    simpa using h
  · rw [Finset.prod_biUnion]
    · refine Finset.prod_eq_one fun v _ => ?_
      have := hχ.1 v (k v)
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at this
      rw [← Units.coe_prod, Units.val_eq_one, ← this]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← (mem_aboveF v P).1 hP]; rfl
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]

end General

theorem finite_idele_base_trivial : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  intro D c χ hc hχ a ha
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let α : (Af D.host.F)ˣ := Units.map (sndA D.host.F).toRingHom.toMonoidHom a
  let f : Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))
  have hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ => rfl
  have hf : ∀ k : D.host.F, f (algebraMap D.host.F _ k) = algebraMap D.host.E _ (algebraMap D.host.F D.host.E k) := by
    intro k
    rw [hfa, ← h1, algebraMap_tmul_one]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (b : Af D.host.F) (n : ℕ),
      Valued.v (b (P.under (𝓞 D.host.F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)) := by
    intro P b n h
    have := h3 b 0 P n (by rwa [map_zero, sub_zero])
    rwa [map_zero, map_zero, sub_zero] at this
  have hfin : ι (finPart D (idF D a : AE D)) = f α := rfl
  obtain ⟨S, k, hS, hS', hp⟩ := exists_approx f hf h0 χ hχ N hN α
  rw [← hfin] at hS hS'
  exact Circle.ext ((hprod (idF D a) ha S k hS hS').trans hp)

end GlobalTheory.BaseIdeleTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdelesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicCharacter_trivial_baseFiniteIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  first | exact @GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | exact GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | (intros; apply GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedSplit

open GlobalTheory.SplitIdem GlobalTheory.IdemModTwo

theorem idem_alg {T : Type} [CommRing T] (p U R w w' : T) (hU : p * U = U)
    (hR : R * R - (w + w') * R + w * w' * p = 0) (hδ : (w + w') * U - 2 * (U * R) = p) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * w' - U * R) = 0 ∧
      (U * w - U * R) + (U * w' - U * R) = p := by
  have h2 : (U * w - U * R) * (U * w' - U * R) = 0 := by
    linear_combination U * U * hR - w * w' * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] [Algebra F K] (φ : K →ₙ+* A)
    (hφ : ∀ (t : F) (y : K), φ (algebraMap F K t * y) = algebraMap F A t * φ y)
    (c : A ⊗[F] E →+* A ⊗[F] E) (a b : E) (t n : F) (r u : K)
    (hc1 : ∀ x : A, c (x ⊗ₜ 1) = x ⊗ₜ 1) (hca : ∀ x : A, c (x ⊗ₜ a) = x ⊗ₜ b)
    (ht : algebraMap F E t = a + b) (hn : algebraMap F E n = a * b)
    (hr : r * r - algebraMap F K t * r + algebraMap F K n = 0) (hu : u * (algebraMap F K t - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ a + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have hF : ∀ s : F, j (algebraMap F A s) = k (algebraMap F E s) := fun s => by
    have h := hjk 1 (algebraMap F E s)
    rw [tmul_algebraMap_eq, mul_one, map_one, one_mul] at h
    exact h
  have h1 : e = j (φ u) * k a - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * k b - j (φ u) * j (φ r) := by
    rw [he, map_add (f := _), hc1, hca, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - algebraMap F A t * φ r + algebraMap F A n * φ 1 = 0 := by
      rw [← hφ, ← hφ, ← map_mul, ← map_sub, ← map_add (f := _), mul_one, hr, map_zero]
    have h := congrArg j this
    rwa [map_add, map_sub, map_mul, map_mul, map_mul, hF, hF, ht, hn, map_add, map_mul, map_zero] at h
  · have : algebraMap F A t * φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← hφ, ← map_mul, ← map_add (f := _), ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_mul, map_ofNat, hF, ht, map_add] at h

theorem exists_root (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n : 𝓞 F)
    (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ r u : v.adicCompletionIntegers F,
      r * r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = 0 ∧
      u * (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : algebraMap (𝓞 F) (v.adicCompletionIntegers F) n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h hn
  have hT : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) :=
    (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = T at hT
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = N at hm
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N) (by monicity!) 0
    (by simpa using hm) (by simpa using hT.map _)
  rw [sub_zero] at hr0
  have hunit : IsUnit (T - 2 * r) := by
    by_contra h
    have h1 : T - 2 * r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    have h2 := Ideal.add_mem _ h1 (Ideal.mul_mem_left _ 2 hr0)
    rw [sub_add_cancel] at h2
    exact h2 hT
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

theorem exists_int (D : D7) (x : 𝓞 D.host.E) (hx : star (x : D.host.E) = x) :
    ∃ t : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = x ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = x := by
  obtain ⟨t, ht⟩ := exists_of_star_eq D hx
  have hxint : IsIntegral ℤ (x : D.host.E) := x.2
  have hi : IsIntegral ℤ t :=
    (isIntegral_algebraMap_iff).1 (ht ▸ hxint)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.UnRep.SplitPl (GlobalTheory.Member.cF D) v → ∃ e : Formalism.L2.Theta.AE D, GlobalTheory.IdemModTwo.SplitAt D v e := by
  rintro D v ⟨P, hP, hPv, a, ha, b, hb, hbP⟩
  have hb' : (b : D.host.E) = star (a : D.host.E) := hb
  obtain ⟨t, ht, ht'⟩ := exists_int D (a + b) (by
    show star ((a : D.host.E) + b) = (a : D.host.E) + b
    rw [hb', star_add, star_star, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int D (a * b) (by
    show star ((a : D.host.E) * b) = (a : D.host.E) * b
    rw [hb', star_mul', star_star, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v t n htv hnv
  have key := idem_tensor (placeHom D.host.F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV D.host.F v _ = algebraMap D.host.F (Af D.host.F) s * singleV D.host.F v y
      rw [singleV_mul, AlgHom.commutes])
    (cA D) (a : D.host.E) (b : D.host.E) (t : D.host.F) (n : D.host.F) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun x => by rw [cA_tmul, star_one]) (fun x => by rw [cA_tmul, hb']) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key⟩

end GlobalTheory.MovedSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick.AtData

theorem weierstrass_translate_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem half_gen {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) : ∃ v : ℂ, v ∉ Λ ∧ InRationalLattice Λ v := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hlat
  refine ⟨w₁ / 2, ?_, ⟨2, by norm_num, ?_⟩⟩
  · intro h
    rw [AddSubgroup.mem_closure_pair] at h
    obtain ⟨m, n, hmn⟩ := h
    have key := (LinearIndependent.pair_iff.1 hli) ((m : ℝ) - 1 / 2) (n : ℝ) (by
      have e : (m : ℂ) * w₁ + (n : ℂ) * w₂ = w₁ / 2 := by simpa [zsmul_eq_mul] using hmn
      simp only [Complex.real_smul]
      push_cast
      linear_combination e)
    have h1 : (m : ℝ) = 1 / 2 := by linarith [key.1]
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have : (2 : ℂ) * (w₁ / 2) = w₁ := by ring
    push_cast
    rw [this]
    exact AddSubgroup.subset_closure (by simp)

theorem atData : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  intro D p _ cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  obtain ⟨v, hv, hvq⟩ := half_gen hlat'
  refine ⟨hok.2.1, hlat', h2, h3, ⟨hlat'.differentiable, fun n => ?_⟩, v, hv, (hwp v hvq hv).1⟩
  have := huse 0 ⟨1, one_pos, by simp⟩ n
  rwa [weierstrass_translate_zero_eq_self] at this

end GlobalTheory.FrobStick.AtData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicDataStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  first | exact @GlobalTheory.FrobStick.AtData.atData | exact GlobalTheory.FrobStick.AtData.atData | (intros; apply GlobalTheory.FrobStick.AtData.atData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_atU {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) (hσ : AlgEnt (sgStar g.abelian₂)) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  have h0 : coef1 (sgStar g.abelian₂) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar g.abelian₂)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar g.abelian₂) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  have hS' : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * PowerSeries.map g.lam S := by
    rw [GlobalTheory.EvenTheta.Param.theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X]
  have hE := GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g _ hS'
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, hS', subst_mul hs, subst_X hs, mul_assoc, mul_assoc, hE]

theorem colAB_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hT, hC, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨aT, eT⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have e1 := sgStar_atU g hL hσ
  obtain ⟨⟨a2, e2⟩, -⟩ := hT _ _ hσ hσ
  obtain ⟨⟨a3, e3⟩, -⟩ := hT _ _ a2 hσ
  obtain ⟨aw, ew⟩ := hC _ hw
  obtain ⟨⟨a4, e4⟩, -⟩ := hT _ _ aw a2
  obtain ⟨-, a5, e5⟩ := hT _ _ aT a4
  obtain ⟨⟨a6, e6⟩, -⟩ := hT _ _ hσ a5
  have hA : colA g.abelian₂ = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z * sgStar g.abelian₂ z := by
    funext z; rw [colA]; ring
  have hB : colB g.abelian₂ v = fun z => sgStar g.abelian₂ z *
      (sqTh g.abelian₂ v z + wpF g.abelian₂ v * (sgStar g.abelian₂ z * sgStar g.abelian₂ z)) := by
    funext z; rw [colB]; ring
  rw [hA, hB]
  refine ⟨a3, a6, e1, ?_, ?_⟩
  · rw [e3, e2, e1, map_pow]; ring
  · rw [e6, e5, e4, e2, ew, eT, e1, lineSer, xAt]
    simp only [map_mul, map_pow, map_sub]
    ring

end GlobalTheory.FrobStick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  first | exact @GlobalTheory.FrobStick.colAB_atU | exact GlobalTheory.FrobStick.colAB_atU | (intros; apply GlobalTheory.FrobStick.colAB_atU <;> assumption)
end
end

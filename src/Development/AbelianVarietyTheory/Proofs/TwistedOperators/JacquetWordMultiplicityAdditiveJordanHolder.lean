module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.Exponents.Additive

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_mem_twKer {ρ : Representation F G V} {σ : Representation F G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (N : Subgroup G) {w : W}
    (hw : w ∈ twKer σ N 1) : ∃ v ∈ twKer ρ N 1, p v = w := by
  have : twKer σ N 1 ≤ (twKer ρ N 1).map p.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨_, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
    simp [p.isIntertwining])
  exact this hw

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem wordMult_exact {π : Representation ℂ (GL (Fin n) k) V}
    {π₁ : Representation ℂ (GL (Fin n) k) W} {π₂ : Representation ℂ (GL (Fin n) k) U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hπ : IsSmooth π)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p)
    (w : List ℂˣ) : wordMult π w = wordMult π₁ w + wordMult π₂ w := by
  unfold wordMult
  split_ifs
  swap
  · simp
  refine jhMult_exact (compMap (jacMap (points _) ι) _) (compMap (jacMap (points _) p) _)
    (isIrreducible_ofChar _) (GlobalTheory.T.jacquetModule_map_injective_of_injective k _ _ _ (points _) W V π₁ π ι hπ hι) (fun x => ?_)
    (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k (points (Fin n))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem wordMult_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin n) k) V)
    (w : List ℂˣ) : wordMult π w = 0 := by
  unfold wordMult
  split_ifs
  · have : Subsingleton (Jacquet π (unipB k (Fin n))) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
  · rfl

theorem sum_add {I : Type 1} (f : I → ℕ∞) (x y : I →₀ ℤ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c) :
    ((x + y).sum fun c a => (a.toNat : ℕ∞) * f c) =
      (x.sum fun c a => (a.toNat : ℕ∞) * f c) + y.sum fun c a => (a.toNat : ℕ∞) * f c := by
  classical
  rw [Finsupp.sum_of_support_subset (x + y) Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset x Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset y Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finsupp.add_apply, Int.toNat_add (hx c) (hy c), Nat.cast_add, add_mul]

theorem wordMult_eq_sum (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (hπ : IsSmooth π) (w : List ℂˣ) :
    wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have hfl : ∀ S : Subrepresentation π, HasFiniteLength S.toRepresentation := fun S =>
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation π
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩) Subtype.val_injective
  have hsm : ∀ S : Subrepresentation π, IsSmooth S.toRepresentation := fun S =>
    (IsSubquotient.of_injective (σ := S.toRepresentation) (ρ := π)
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, wordMult S.toRepresentation w =
      (cls S.toRepresentation (hfl S)).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h0 : cls (⊥ : Subrepresentation π).toRepresentation (hfl ⊥) = 0 := by
        ext c
        simp [cls_apply, jhMult_of_subsingleton (IrrRep.irr _)]
      rw [h0, wordMult_of_subsingleton, Finsupp.sum_zero_index]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hι : Function.Injective ι := Submodule.inclusion_injective hT.le
    have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
    have he : Function.Exact ι p := fun v =>
      ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩
    let σ : IrrRep (GL (Fin n) k) :=
      ⟨_, subQuot S T, (IsSubquotient.of_surjective p hps).isSmooth (hsm S),
        isIrreducible_subQuot hT⟩
    have hσ : cls (subQuot S T) σ.hasFiniteLength = Finsupp.single σ.cl 1 := cls_irr σ _
    obtain ⟨ψ⟩ := σ.nonempty_equiv_rep
    rw [wordMult_exact ι p (hsm S) hι hps he, cls_exact ι p hι hps he _ (hfl T) σ.hasFiniteLength,
      sum_add _ _ _ (fun c => by simp [cls_apply]) (fun c => by simp [cls_apply]), ih T hT.lt, hσ,
      Finsupp.sum_single_index (by simp), wordMult_congr ψ]
    simp [σ]
  rw [← wordMult_congr (topEquiv π), key ⊤, cls_congr (topEquiv π) _ h]

theorem wordMult_additive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w :=
  fun _ _ _ _ _ _ _ _ _ π h hπ w => wordMult_eq_sum π h hπ w

end GlobalTheory.SmGL.Exponents.Additive
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolderStatement
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetWordMultiplicity_additive_jordanHolder : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  first | exact @GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | exact GlobalTheory.SmGL.Exponents.Additive.wordMult_additive | (intros; apply GlobalTheory.SmGL.Exponents.Additive.wordMult_additive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialMemRangeGlue
noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt.GlueProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {a b : ℕ}


open Classical in
def rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ)

def ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : LPol b a →ₗ[ℂ] PolF D b a :=
  LinearMap.mulRight ℂ (rest τ P) ∘ₗ (MvPolynomial.rename (fun s => (τ, s))).toLinearMap

theorem ins_apply (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    ins τ P p = MvPolynomial.rename (fun s => (τ, s)) p * rest τ P := rfl

open Classical in
theorem glue_update (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    glue (Function.update P τ p) = ins τ P p := by
  rw [ins_apply, glue, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), rest]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

theorem glue_eq (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : glue P = ins τ P (P τ) := by
  classical
  rw [← glue_update, Function.update_eq_self]

theorem pderiv_other {τ ρ : D.what₂.Tau} (h : ρ ≠ τ) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (MvPolynomial.rename (fun s => (ρ, s)) p : PolF D b a) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    rw [map_mul, Derivation.leibniz, hp, MvPolynomial.rename_X, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e
      exact h (congrArg Prod.fst e)

theorem pderiv_rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) :
    MvPolynomial.pderiv (τ, s) (rest τ P) = 0 := by
  classical
  unfold rest
  refine Finset.prod_induction _ (fun q : PolF D b a => MvPolynomial.pderiv (τ, s) q = 0) ?_ ?_ ?_
  · intro x y hx hy
    rw [Derivation.leibniz, hx, hy]; simp
  · simp
  · intro ρ hρ
    exact pderiv_other (Finset.ne_of_mem_erase hρ) s _

theorem pderiv_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (ins τ P p) = ins τ P (MvPolynomial.pderiv s p) := by
  classical
  have hinj : Function.Injective (fun s : Fin b × Fin a => (τ, s)) := fun x y e => congrArg Prod.snd e
  have := MvPolynomial.pderiv_rename hinj s p
  rw [ins_apply, ins_apply, Derivation.leibniz, pderiv_rest, ← this]
  simp [mul_comm]

theorem mul_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.X (τ, s) * ins τ P p = ins τ P (MvPolynomial.X s * p) := by
  rw [ins_apply, ins_apply, map_mul, MvPolynomial.rename_X, mul_assoc]

theorem rai_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : raiO τ ε ε' i j (ins τ P p) = ins τ P (rai ε ε' i j p) := by
  unfold raiO rai
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, map_neg, Derivation.coeFn_coe]
    rw [← pderiv_ins]

theorem low_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : lowO τ ε ε' i j (ins τ P p) = ins τ P (low ε ε' i j p) := by
  unfold lowO low
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe]
    rw [← pderiv_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]

theorem fockS_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (X : Matrix (Fin a) (Fin a) ℂ) (p : LPol b a) :
    fockS τ ε ε' X (ins τ P p) = ins τ P (locS ε ε' X p) := by
  unfold fockS locS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem fockT_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin b) (Fin b) ℂ) (p : LPol b a) :
    fockT τ ε ε' Y (ins τ P p) = ins τ P (locT ε ε' Y p) := by
  unfold fockT locT
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem glue_span :
    Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | (apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue ..)

theorem glueLaw : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  intro D a b
  refine ⟨glue_span, fun τ ε ε' P => ⟨fun X => ?_, fun Y => ?_⟩⟩
  · rw [glue_update, glue_eq τ P, fockS_ins]
  · rw [glue_update, glue_eq τ P, fockT_ins]

end GlobalTheory.Chain.RealIt.GlueProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluing_law_holds : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  first | exact @GlobalTheory.Chain.RealIt.GlueProof.glueLaw | exact GlobalTheory.Chain.RealIt.GlueProof.glueLaw | (intros; apply GlobalTheory.Chain.RealIt.GlueProof.glueLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.StabLatInv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem intGL_mulVec_mem (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : ∀ i, x i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    (intGL F E n y).val.mulVec x i ∈ Formalism.L2.Herm.intAf F E := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => mul_mem (y.val i j).2 (hx j)

theorem isFrame_mul_of_mem_St (β k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hk : k ∈ St β) : IsFrame (k * β) Λ := by
  obtain ⟨y, hy⟩ := hk
  have e : k * β = β * intGL F E n y := by
    rw [← hy]
    change β * intGL F E n y * β⁻¹ * β = _
    rw [inv_mul_cancel_right]
  intro x
  rw [hβ x, e, mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · exact intGL_mulVec_mem y⁻¹ _
  · intro h
    have h2 := intGL_mulVec_mem y _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2

end General

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh u
  have hS' := isFrame_mul_of_mem_St βS _ ΛS hS hg
  have hT' := isFrame_mul_of_mem_St βT _ ΛT hT hh
  have eS : (finE S g * βS).val = (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.val := rfl
  have eT : (finE T h * βT).val = (Formalism.L2.Theta.mt T h).map (toEAf D) * βT.val := rfl
  constructor
  · exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS hS' hT hT' eS eT u
  · intro hu
    have h1 := GlobalTheory.AdelicLatMove.actO_mem_latO S T g⁻¹ h⁻¹ ΛS ΛS ΛT ΛT _ βS _ βT hS' hS hT' hT
      (GlobalTheory.AdelicLatMove.frame_inv S g _ _ eS) (GlobalTheory.AdelicLatMove.frame_inv T h _ _ eT) _ hu
    have h2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at h2
    rwa [h2] at h1

end GlobalTheory.StabLatInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMemStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.StabLatInv.mem_latO_iff_actO_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompFinIdemSum

variable {D : D7}

theorem compFin_tensAt_ne {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E u (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    have h0 : evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) = 0 := evalV_singleFin_ne h a
    have h1 : compFin D.host.F D.host.E u (pairA D.host.F 0 (singleFin v a) ⊗ₜ[D.host.F] x) =
        evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) ⊗ₜ[D.host.F] x :=
      Algebra.TensorProduct.map_tmul ..
    rw [h1, h0, TensorProduct.zero_tmul]
  | add y z hy hz => simp only [map_add (f := _), hy, hz, add_zero]


set_option maxHeartbeats 1000000 in
open Classical in
theorem compFin_add_cA_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z,
    compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  intro D Z e he PP hPP
  classical
  obtain ⟨⟨es, hes, rfl⟩, hcc⟩ := he
  obtain ⟨v0, τ0, -, hPP0⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes PP hPP)
  have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v0 := by rw [hPP0]; exact splitPrime_under τ0
  rw [hu]
  have key : ∀ Q ∈ Z, compFin D.host.F D.host.E v0 (es Q) =
      (if Q = PP then splitIdem (isCMExt_host D) τ0 else 0) +
        (if Q = splitPrime (τ0.comp D.sp.cm.sig) then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    intro Q hQ
    obtain ⟨v, τ, hI, hQτ⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes Q hQ)
    have hQv : Q.under (𝓞 D.host.F) = v := by rw [hQτ]; exact splitPrime_under τ
    rw [GlobalTheory.SplitIdemDict.eq_idem hI, GlobalTheory.EmbChart.idem]
    by_cases hv : v = v0
    · subst hv
      rcases eq_or_eq_comp_conj (isCMExt_host D) τ0 τ with h | h <;> rw [h] at hQτ ⊢
      · rw [if_pos (hQτ.trans hPP0.symm), if_neg (by rw [hQτ]; exact (splitPrime_comp_ne (isCMExt_host D) τ0).symm),
          add_zero]
        exact GlobalTheory.EmbChart.compFin_tensAt _ _
      · rw [if_neg (by rw [hQτ, hPP0]; exact splitPrime_comp_ne (isCMExt_host D) τ0), if_pos hQτ, zero_add,
          GlobalTheory.EmbChart.compFin_tensAt, splitIdem_comp]
    · have h1 : Q ≠ PP := fun h => hv (by rw [← hQv, h, hu])
      have h2 : Q ≠ splitPrime (τ0.comp D.sp.cm.sig) := fun h => hv (by rw [← hQv, h]; exact splitPrime_under _)
      rw [if_neg h1, if_neg h2, add_zero]
      exact compFin_tensAt_ne (Ne.symm hv) _
  have hsum : compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q) = splitIdem (isCMExt_host D) τ0 +
      (if splitPrime (τ0.comp D.sp.cm.sig) ∈ Z then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl key]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hPP]
  have hc : compFin D.host.F D.host.E v0 (cA D (∑ Q ∈ Z, es Q)) =
      sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q)) :=
    (GlobalTheory.SplitIdemDict.compFin_cA _).symm
  have h1 : ∀ a : Fv D.host.F v0 ⊗[D.host.F] D.host.E, a + (1 - a) = 1 := fun a => by abel
  rw [map_add (f := _), hc, hsum]
  by_cases hP' : splitPrime (τ0.comp D.sp.cm.sig) ∈ Z
  · exfalso
    have hz := congrArg (compFin D.host.F D.host.E v0) hcc
    rw [map_mul, hc, hsum, if_pos hP', h1, map_one, mul_one, map_zero] at hz
    have h3 := congrArg (fun y => splitProj τ0 y) hz
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  · rw [if_neg hP', add_zero, sigR_splitIdem, h1]

end GlobalTheory.CompFinIdemSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z, compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  first | exact @GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | exact GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | (intros; apply GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjIntegral

theorem mul_int {R : Type} [CommRing R] (S : Subring R) {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin n) : (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem conj_int {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R) (ha : ∀ i j, (a • γ) i j ∈ S) :
    ∀ i j, (σ a • γi) i j ∈ S := by
  have e1 : γi = Gi * (γ.map σ)ᵀ * G := by
    calc γi = Gi * G * γi := by rw [hGG, Matrix.one_mul]
      _ = Gi * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = Gi * (γ.map σ)ᵀ * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = Gi * (γ.map σ)ᵀ * G := by rw [hγ, Matrix.mul_one]
  have e2 : σ a • γi = Gi * ((a • γ).map σ)ᵀ * G := by
    have : (a • γ).map σ = σ a • γ.map σ := by
      ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  have hc : ∀ i j, ((a • γ).map σ)ᵀ i j ∈ S := fun i j => hσ _ (ha j i)
  rw [e2]
  exact mul_int S (mul_int S hGi hc) hG

theorem conj_int_both {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hγ' : γi * γ = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R)
    (ha : ∀ i j, (a • γ) i j ∈ S) (ha' : ∀ i j, (a • γi) i j ∈ S) :
    (∀ i j, (σ a • γ) i j ∈ S) ∧ (∀ i j, (σ a • γi) i j ∈ S) := by
  have hu' : (γi.map σ)ᵀ * G * γi = G := by
    have h1 : (γi.map σ)ᵀ * (γ.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hγ, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    calc (γi.map σ)ᵀ * G * γi = (γi.map σ)ᵀ * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = ((γi.map σ)ᵀ * (γ.map σ)ᵀ) * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hγ, Matrix.one_mul, Matrix.mul_one]
  exact ⟨conj_int S σ hσ G Gi γi γ hG hGi hGG hγ' hu' a ha', conj_int S σ hσ G Gi γ γi hG hGi hGG hγ hu a ha⟩

theorem unit_conj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (B Bi H J : Matrix (Fin n) (Fin n) R)
    (hB : Bi * B = 1) (hB' : B * Bi = 1) (hH : Formalism.UG.cT σ H * J * H = J) :
    ((Bi * H * B).map σ)ᵀ * (Formalism.UG.cT σ B * J * B) * (Bi * H * B) = Formalism.UG.cT σ B * J * B := by
  have hcT : ∀ A C : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ (A * C) = Formalism.UG.cT σ C * Formalism.UG.cT σ A := by
    intro A C; simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have e : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← hcT, hB']
    simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  change Formalism.UG.cT σ (Bi * H * B) * _ * _ = _
  rw [hcT, hcT]
  calc Formalism.UG.cT σ B * (Formalism.UG.cT σ H * Formalism.UG.cT σ Bi) * (Formalism.UG.cT σ B * J * B) * (Bi * H * B)
      = Formalism.UG.cT σ B * (Formalism.UG.cT σ H * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J * (B * Bi) * H) * B := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ B * J * B := by rw [e, hB', Matrix.mul_one, Matrix.mul_one, hH]

end GlobalTheory.ConjIntegral

namespace GlobalTheory.ConjIntegral


set_option maxHeartbeats 800000 in
theorem conj_smul_isIntM : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  intro D T ΛT βT hsd hβ h hh γ hγ a h1 h2
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) T.gram βT ΛT hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  have hσ : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ hx => GlobalTheory.LevSplit.sigR_int hx
  have hGm : ∀ i j, (intGL D.host.F D.host.E T.rank G).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => (G.1 i j).2
  have hGi : ∀ i j, (intGL D.host.F D.host.E T.rank G⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => ((G⁻¹).1 i j).2
  have hGG : (intGL D.host.F D.host.E T.rank G⁻¹).1 * (intGL D.host.F D.host.E T.rank G).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

  have hhu : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h.1 * T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) * h.1 =
      T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) := hh
  have hγ1 : γ.1 = (βT⁻¹).1 * h.1 * βT.1 := by rw [hγ]; rfl
  have hu := unit_conj (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) βT.1 (βT⁻¹).1 h.1 _
    (Units.inv_mul βT) (Units.mul_inv βT) hhu
  rw [← hγ1, ← hG] at hu
  have key := conj_int_both _ _ hσ _ _ γ.1 (γ⁻¹).1 hGm hGi hGG (Units.mul_inv γ) (Units.inv_mul γ) hu (toEAf D a) h1 h2
  rw [GlobalTheory.AdelicLatMove.toEAf_cA a]
  exact key

end GlobalTheory.ConjIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  first | exact @GlobalTheory.ConjIntegral.conj_smul_isIntM | exact GlobalTheory.ConjIntegral.conj_smul_isIntM | (intros; apply GlobalTheory.ConjIntegral.conj_smul_isIntM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesClosed

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

def lowPart {m : ℕ} (M : Mx D m m) : Mx D m m := Matrix.of fun i j => if j ≤ i then M i j else 0

theorem continuous_lowPart {m : ℕ} : Continuous (lowPart (D := D) (m := m)) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Mx D m m => if j ≤ i then a i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem lowPart_eq_iff {m : ℕ} (M : Mx D m m) :
    lowPart M = lowPart 1 ↔ ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1 := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, ?_⟩
    · have := congrFun (congrFun h i) j
      simp only [lowPart, Matrix.of_apply, if_pos hji.le] at this
      rwa [Matrix.one_apply_ne hji.ne'] at this
    · have := congrFun (congrFun h i) i
      simp only [lowPart, Matrix.of_apply, if_pos (le_refl i), Matrix.one_apply_eq] at this
      exact this
  · intro h
    ext i j
    simp only [lowPart, Matrix.of_apply]
    split_ifs with hji
    · rcases hji.lt_or_eq with hlt | heq
      · rw [(h i j).1 hlt, Matrix.one_apply_ne hlt.ne']
      · subst heq; rw [(h j j).2, Matrix.one_apply_eq]
    · rfl

theorem strictUp_sub_one {m : ℕ} {M : Mx D m m} (h : ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1) :
    GlobalTheory.BesselChar.StrictUp (M - 1) := by
  intro j i hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [Matrix.sub_apply, (h j i).1 hlt, Matrix.one_apply_ne hlt.ne', sub_zero]
  · subst heq; rw [Matrix.sub_apply, (h i i).2, Matrix.one_apply_eq, sub_self]

theorem mem_jacGrp_iff_mat (g : GA D S) : g ∈ jacGrp d ↔
    (d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧
      ∀ i j : Fin ρ, (j < i → (d.pX ⬝ (mt S g ⬝ d.jX)) i j = 0) ∧ (d.pX ⬝ (mt S g ⬝ d.jX)) i i = 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
    have e : mt S (d.levi u * (d.nB b * d.nC c) * d.emb0 h) ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, GlobalTheory.MixPer.Decomp.mt_flag_jX]
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.pY_jX, d.pX_jX, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.one_mul]
    exact ⟨rfl, rfl, fun i j => hu i j⟩
  · rintro ⟨h0, hY, hX⟩
    obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit (strictUp_sub_one hX)
    have hu' : u.1 = d.pX ⬝ (mt S g ⬝ d.jX) := by rw [hu1, add_sub_cancel]
    have hgX : mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [hu']
      conv_lhs => rw [GlobalTheory.MixPer.Decomp.decomp d (mt S g ⬝ d.jX)]
      rw [h0, hY, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have hst : (d.levi u)⁻¹ * g ∈ stabX d := mem_fixer.2 (GlobalTheory.MixPer.Decomp.fix_of_eq (by rw [d.levi_jX, hgX]))
    obtain ⟨n, hn, h, hnh⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hst
    have hn' : n ∈ flagN d := (Subgroup.mem_inf.1 (show n ∈ flagN d ⊓ fixer S d.jX from hn)).1
    have e : g = d.levi u * n * d.emb0 h := by rw [mul_assoc, ← hnh, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (d.levi_mem_NFlag hu) hn')) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem jacGrp_closed : IsClosed (jacGrp d : Set (GA D S)) := by
  haveI : T2Space (Mx D S₀.rank ρ) := (lattice_Mx D _ _).2.2.2.1
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D _ _).2.2.2.1
  have hc : Continuous fun g : GA D S => mt S g ⬝ d.jX := (continuous_mt S).matrix_mul continuous_const
  have e : (jacGrp d : Set (GA D S)) = {g | d.p0 ⬝ (mt S g ⬝ d.jX) = 0} ∩ {g | d.pY ⬝ (mt S g ⬝ d.jX) = 0} ∩
      {g | lowPart (d.pX ⬝ (mt S g ⬝ d.jX)) = lowPart 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_jacGrp_iff_mat, Set.mem_inter_iff, Set.mem_setOf_eq, lowPart_eq_iff, and_assoc]
  rw [e]
  exact ((isClosed_eq (continuous_const.matrix_mul hc) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul hc) continuous_const)).inter
    (isClosed_eq (continuous_lowPart.comp (continuous_const.matrix_mul hc)) continuous_const)

theorem flagUnipotent_anisotropic_projection_eq_one {n : GA D S} (hn : n ∈ flagN d) : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [d.nC_j0, d.nB_j0, ← Matrix.mul_assoc d.p0 (mt S (d.levi u)), d.wittDecomp_projAnisotropic_levi, Matrix.mul_add, d.p0_j0,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n) d.j0, ← Matrix.mul_assoc d.p0, flagUnipotent_anisotropic_projection_eq_one d hn,
    Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem exists_emb_of_fix {k : GA D S₀} (hk : mt S₀ k ⬝ o.jB = o.jB) : ∃ a : GA D A, o.emb (a, 1) = k := by
  have h1 : o.pB ⬝ (mt S₀ k ⬝ o.jA) = 0 := by
    have e : adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) = 0 := by
      conv_lhs => rw [← hk]
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
        ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_BA]
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mx D A.rank A.rank, M = o.pA ⬝ (mt S₀ k ⬝ o.jA) := ⟨_, rfl⟩
  have hA : mt S₀ k ⬝ o.jA = o.jA ⬝ M := by
    calc mt S₀ k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ M := by rw [Matrix.add_mul, Matrix.mul_assoc o.jB, h1, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hM]
  have hu : adj M * (gA A * M) = gA A := by
    calc adj M * (gA A * M) = adj (o.jA ⬝ M) ⬝ (gA S₀ ⬝ (o.jA ⬝ M)) := by
          rw [adj_mul, ← o.gram_AA]; simp only [Matrix.mul_assoc]
      _ = adj (mt S₀ k ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) := by rw [hA]
      _ = gA A := by
          rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
            ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_AA]
  have key : mt S₀ k = o.jA ⬝ M ⬝ o.pA + o.jB ⬝ o.pB := by
    have e : mt S₀ k ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ k := by rw [o.sum_eq_one]; exact Matrix.mul_one _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hk] at e
    exact e.symm
  exact ⟨ofMat A M hu, mt_injective S₀ (by rw [o.mt_emb, mt_ofMat, mt_one, Matrix.mul_one, key])⟩

def prodSub : Subgroup (GA D S) where
  carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
    refine ⟨n * (embA d o h * n' * (embA d o h)⁻¹), mul_mem hn ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n' hn' _), h * h', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨n, hn, h, rfl⟩
    refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, (GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 _ (inv_mem hn) _, h⁻¹, ?_⟩
    rw [map_inv]; group

theorem besGrp_le_prodSub : besGrp d o ≤ prodSub d o :=
  sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)

theorem besGrp_eq_inter :
    (besGrp d o : Set (GA D S)) = (jacGrp d : Set (GA D S)) ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) ⬝ o.jB = o.jB} := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := besGrp_le_prodSub d o hg
    refine ⟨mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨o.emb (h, 1), rfl⟩), ?_⟩
    show d.p0 ⬝ (mt S (n * d.emb0 (o.emb (h, 1))) ⬝ d.j0) ⬝ o.jB = o.jB
    rw [witt_anisotropic_block_flag_mul_embedded d hn, o.emb_jB, mt_one, Matrix.mul_one]
  · rintro ⟨hg, he⟩
    obtain ⟨n, hn, k, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    have he' : d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) ⬝ o.jB = o.jB := he
    rw [witt_anisotropic_block_flag_mul_embedded d hn] at he'
    obtain ⟨a, ha⟩ := exists_emb_of_fix o he'
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, by rw [embA_apply, ha]⟩)

theorem besGrp_isClosed : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    IsClosed (besGrp d o : Set (GA D S)) := by
  intro D S S₀ A L ρ d o
  rw [besGrp_eq_inter]
  haveI : T2Space (Mx D S₀.rank L.rank) := (lattice_Mx D _ _).2.2.2.1
  exact (jacGrp_closed d).inter (isClosed_eq
    ((continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)).matrix_mul continuous_const)
    continuous_const)

end GlobalTheory.BesClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.SubstDeg

theorem totalDegree_aeval_le {σ κ : Type*} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (AddMonoidAlgebra.coeff P s)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_subst_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  intro D a b τ ε ε' g k P
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs with h
  · refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
    refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le
  all_goals first
    | exact (MvPolynomial.totalDegree_X _).le
    | (refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
       refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
       exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le)

end GlobalTheory.Chain.RealIt.SubstDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_total_degree_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  first | exact @GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le | exact GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le | (intros; apply GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSquare

theorem thetaFunctions_squareIntegrable_heisenbergUnitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.ThetaSquareIntegrable D :=
  GlobalTheory.ThetaSquare.theta_square_integrable

end GlobalTheory.ThetaSquare
end

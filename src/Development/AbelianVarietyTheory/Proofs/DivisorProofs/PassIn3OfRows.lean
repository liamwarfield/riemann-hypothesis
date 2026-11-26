module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReordEqConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatMuPOfRowTest
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Formalism.IndefR.Rat Formalism.IndefR.Cx.CxData in
theorem ratMuP_of_rowTest : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PrincipalLevelBijective F → (R.toCx3 F).RATmu (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall⟩ := hH2
  intro t i k
  have hmem : (R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat _ ψ hψ ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) hinj0
    (fun j l => by rw [CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _)
    (solve ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0)
      ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesCardAndResidueLe
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum
open Formalism.L2.DIV NumberField Module

noncomputable section

namespace GlobalTheory.multiplicity_linearCharacter_eq_characterSum

theorem nOf_eq_charSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  intro K _ _ G _ _ W _ _ _ τ H _ ψ
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have hep : Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩ = (Nat.card H : K)⁻¹ • T := by
    unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp
    congr 1
    rw [hT]
    simp only [map_inv]
    congr!
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hid : IsIdempotentElem (Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩) := by
    rw [IsIdempotentElem, hep, smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← htr, hep, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.multiplicity_linearCharacter_eq_characterSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSumStatement
open Formalism.L2.DIV NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  first | exact @GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | exact GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum | (intros; apply GlobalTheory.multiplicity_linearCharacter_eq_characterSum.nOf_eq_charSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
open GlobalTheory.FinGL Formalism.L2.DIV Module

noncomputable section

namespace GlobalTheory.MultOneRealised

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

def leftReg (K G : Type) [Field K] [Group G] : Representation K G (MonoidAlgebra K G) where
  toFun g := LinearMap.mulLeft K (MonoidAlgebra.single g 1)
  map_one' := by rw [← MonoidAlgebra.one_def]; exact LinearMap.mulLeft_one K _
  map_mul' a b := by
    refine LinearMap.ext fun v => ?_
    simp [← mul_assoc, MonoidAlgebra.single_mul_single]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
private lemma natCast_smul_eq_trace_smul_one_of_commute {L G : Type} [Field L] [Group G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (T : Module.End L (Fin n → L)) (hT : ∀ g, T * ρ g = ρ g * T) :
    (n : L) • T = LinearMap.trace L _ T • 1 := by
  haveI : Nontrivial (ρ.IntertwiningMap ρ) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : ρ.IntertwiningMap ρ) one_ne_zero).1 h1
    ⟨T, fun g => hT g⟩
  have hT' : T = c • 1 := by
    have := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Representation.IntertwiningMap.toLinearMap_smul] at this
    have h' : c • (1 : Module.End L (Fin n → L)) = T := this
    exact h'.symm
  subst hT'
  simp [LinearMap.trace_one, mul_comm, smul_smul]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
private lemma natCast_mul_sum_trace_conj_eq_mul_trace {L G : Type} [Field L] [Group G] [Fintype G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (a b : G) :
    (n : L) * ∑ x : G, LinearMap.trace L _ (ρ (a * (x * b * x⁻¹))) =
      Fintype.card G * LinearMap.trace L _ (ρ b) * LinearMap.trace L _ (ρ a) := by
  set T : Module.End L (Fin n → L) := ∑ x : G, ρ x * ρ b * ρ x⁻¹ with hTdef
  have hT : ∀ g, T * ρ g = ρ g * T := by
    intro g
    rw [hTdef, Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft, ← map_mul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have key := natCast_smul_eq_trace_smul_one_of_commute ρ h1 T hT
  have htr : LinearMap.trace L _ T = Fintype.card G * LinearMap.trace L _ (ρ b) := by
    have hx : ∀ x : G, LinearMap.trace L _ (ρ x * ρ b * ρ x⁻¹) = LinearMap.trace L _ (ρ b) := by
      intro x
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hTdef, map_sum]
    simp [hx]
  have := congrArg (fun S => LinearMap.trace L _ (ρ a * S)) key
  simp only [mul_smul_comm, map_smul, mul_one, smul_eq_mul] at this
  rw [htr] at this
  rw [← this, hTdef]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, map_mul, mul_assoc]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
private lemma trace_rep_conj_eq {L G : Type} [Field L] [Group G] {V : Type} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (g y : G) :
    LinearMap.trace L V (ρ (g * y * g⁻¹)) = LinearMap.trace L V (ρ y) := by
  rw [map_mul ρ (g * y), map_mul ρ g, LinearMap.trace_mul_comm L (ρ g * ρ y) (ρ g⁻¹), ← mul_assoc,
    ← map_mul ρ g⁻¹ g, inv_mul_cancel, map_one, one_mul]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
private lemma natCast_mul_sum_trace_inv_mul_trace_mul_eq {L G : Type} [Field L] [Group G] [Fintype G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (hpair : ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) * LinearMap.trace L _ (ρ y) = Fintype.card G)
    (b : G) :
    (n : L) * ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) * LinearMap.trace L _ (ρ (y * b)) =
      Fintype.card G * LinearMap.trace L _ (ρ b) := by
  set Z : Module.End L (Fin n → L) := ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) • ρ y with hZdef
  have hZ : ∀ g, Z * ρ g = ρ g * Z := by
    intro g
    rw [hZdef, Finset.sum_mul, Finset.mul_sum]
    symm
    refine Fintype.sum_equiv ((MulAut.conj g).toEquiv) _ _ fun y => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, mul_inv_rev,
      inv_inv, smul_mul_assoc, mul_smul_comm, ← map_mul]
    rw [← mul_assoc g, trace_rep_conj_eq, inv_mul_cancel_right]
  have key := natCast_smul_eq_trace_smul_one_of_commute ρ h1 Z hZ
  have htr : LinearMap.trace L _ Z = Fintype.card G := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hZdef, map_sum, ← hpair]
    simp
  have := congrArg (fun S => LinearMap.trace L _ (S * ρ b)) key
  simp only [smul_mul_assoc, map_smul, one_mul, smul_eq_mul, htr] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← this, hZdef, Finset.sum_mul, map_sum]
  simp [map_mul, smul_mul_assoc]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
private lemma trace_leftReg_mul_mulRight_eq_sum_coeff {K G : Type} [Field K] [Group G] [Fintype G]
    (f : MonoidAlgebra K G) (t : G) :
    LinearMap.trace K _ (_root_.GlobalTheory.MultOneRealised.leftReg K G t * LinearMap.mulRight K f) =
      ∑ x : G, f.coeff (x⁻¹ * t⁻¹ * x) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K), Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  simp only [_root_.GlobalTheory.MultOneRealised.leftReg, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one]
  simp [MonoidAlgebra.basis, MonoidAlgebra.single_mul_apply, mul_assoc]


open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
theorem _root_.GlobalTheory.MultOneRealised.exists_rep_of_mult_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), _root_.Formalism.L2.DIV.IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  intro K _ _ G _ _ χ hχ P _ ψ hsum
  classical
  obtain ⟨n₀, ρ, hirr, hch⟩ := hχ
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  have hch' : ∀ g, LinearMap.trace (AlgebraicClosure K) _ (ρ g) =
      algebraMap K (AlgebraicClosure K) (χ g) := hch
  have hirrc : _root_.GlobalTheory.BI.IsIrrChar (AlgebraicClosure K) (AlgebraicClosure K)
      (fun g => algebraMap K (AlgebraicClosure K) (χ g)) :=
    ⟨n₀, ρ, hirr, fun g => by rw [hch g]; rfl⟩
  have hp1 := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed _ G _ hirrc
  have hp2 := _root_.GlobalTheory.BI.pair_character_eq_finrank (AlgebraicClosure K)
    (AlgebraicClosure K) G _ _ ρ ρ
  have hfun : (fun g => algebraMap (AlgebraicClosure K) (AlgebraicClosure K) (ρ.character g)) =
      fun g => algebraMap K (AlgebraicClosure K) (χ g) := by
    funext g; rw [hch g]; rfl
  rw [hfun, hp1] at hp2
  have h1 : Module.finrank (AlgebraicClosure K) (ρ.IntertwiningMap ρ) = 1 := by
    exact_mod_cast hp2.symm
  have hpair : ∑ y : G, LinearMap.trace (AlgebraicClosure K) _ (ρ y⁻¹) *
      LinearMap.trace (AlgebraicClosure K) _ (ρ y) = Fintype.card G := by
    have := hp1
    unfold _root_.GlobalTheory.BI.pair at this
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
      inv_mul_eq_one₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] at this
    rw [this]
    exact Finset.sum_congr rfl fun y _ => by rw [hch', hch', mul_comm]
  have hn : algebraMap K (AlgebraicClosure K) (χ 1) = n₀ := by
    rw [← hch', map_one, LinearMap.trace_one, Module.finrank_fin_fun]
  have hAv : ∀ a b : G, (n₀ : AlgebraicClosure K) *
      ∑ x : G, algebraMap K (AlgebraicClosure K) (χ (a * (x * b * x⁻¹))) =
      Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b) *
        algebraMap K (AlgebraicClosure K) (χ a) := by
    intro a b
    have := natCast_mul_sum_trace_conj_eq_mul_trace ρ h1 a b
    simpa only [hch'] using this
  have hO : ∀ b : G, (n₀ : AlgebraicClosure K) * ∑ y : G, algebraMap K (AlgebraicClosure K) (χ y⁻¹) *
      algebraMap K (AlgebraicClosure K) (χ (y * b)) =
      Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b) := by
    intro b
    have := natCast_mul_sum_trace_inv_mul_trace_mul_eq ρ h1 hpair b
    simpa only [hch'] using this
  have hcl : ∀ g y : G, algebraMap K (AlgebraicClosure K) (χ (g * y * g⁻¹)) =
      algebraMap K (AlgebraicClosure K) (χ y) := by
    intro g y; rw [← hch', ← hch', trace_rep_conj_eq]
  have hn0 : (n₀ : AlgebraicClosure K) ≠ 0 := by
    obtain ⟨hnt, -⟩ := _root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one _ G _ ρ h1
    rcases Nat.eq_zero_or_pos n₀ with h0 | h0
    · subst h0
      exact absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)
    · exact Nat.cast_ne_zero.2 h0.ne'
  let c : G → K := fun g => χ 1 / (Fintype.card G * Fintype.card P) *
    ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) * χ (h * g⁻¹)
  let f : MonoidAlgebra K G := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hf : ∀ x, f.coeff x = c x := fun x => by simp [f]
  have hP : (Fintype.card P : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hG : (Fintype.card G : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set ι := algebraMap K (AlgebraicClosure K) with hι
  have hsum' : ∑ h : P, ι (χ h) * ι (((ψ h)⁻¹ : Kˣ) : K) = Fintype.card P := by
    have := congrArg ι hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_natCast] using this
  have hψ : ∀ a b : P, ι (((ψ (a * b))⁻¹ : Kˣ) : K) =
      ι (((ψ a)⁻¹ : Kˣ) : K) * ι (((ψ b)⁻¹ : Kˣ) : K) := by
    intro a b; rw [map_mul, mul_inv, Units.val_mul, map_mul]
  have hcyc : ∀ a b : G, ι (χ (a * b)) = ι (χ (b * a)) := by
    intro a b; rw [← hcl a (b * a)]; congr 2; group
  have hidem : f * f = f := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
    simp only [hf]
    apply ι.injective
    have hinner : ∀ h k : G, ∑ y : G, ι (χ (h * y⁻¹)) * ι (χ (k * (y⁻¹ * g)⁻¹)) =
        Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀ := by
      intro h k
      rw [eq_div_iff hn0, ← hO (h * k * g⁻¹), mul_comm]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight h⁻¹) _ _ fun y => ?_
      simp only [Equiv.coe_mulRight]
      rw [show k * (y⁻¹ * g)⁻¹ = k * g⁻¹ * y by group, hcyc (k * g⁻¹) y,
        show (y * h⁻¹)⁻¹ = h * y⁻¹ by group, show y * h⁻¹ * (h * k * g⁻¹) = y * (k * g⁻¹) by group]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, map_sum, map_mul, map_div₀, map_natCast, hn]
    set A : AlgebraicClosure K := (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) with hA
    calc ∑ y : G, (A * ∑ h : P, ι (((ψ h)⁻¹ : Kˣ) : K) * ι (χ (h * y⁻¹))) *
          (A * ∑ k : P, ι (((ψ k)⁻¹ : Kˣ) : K) * ι (χ (k * (y⁻¹ * g)⁻¹)))
        = ∑ y : G, ∑ h : P, ∑ k : P, A * A * (ι (((ψ h)⁻¹ : Kˣ) : K) * ι (((ψ k)⁻¹ : Kˣ) : K)) *
            (ι (χ (h * y⁻¹)) * ι (χ (k * (y⁻¹ * g)⁻¹))) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ h : P, ∑ k : P, A * A * (ι (((ψ h)⁻¹ : Kˣ) : K) * ι (((ψ k)⁻¹ : Kˣ) : K)) *
            (Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum, hinner]
      _ = ∑ h : P, ∑ m : P, A * A * ι (((ψ m)⁻¹ : Kˣ) : K) *
            (Fintype.card G * ι (χ (m * g⁻¹)) / n₀) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun k => ?_
          simp only [Equiv.coe_mulLeft, hψ, Subgroup.coe_mul, mul_assoc]
      _ = A * ∑ m : P, ι (((ψ m)⁻¹ : Kˣ) : K) * ι (χ (m * g⁻¹)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hA]
          field_simp
  have hI2 : ∀ t : G, ∑ x : G, c (x⁻¹ * t⁻¹ * x) = χ t := by
    intro t
    apply ι.injective
    have hx : ∀ h : G, ∑ x : G, ι (χ (h * (x⁻¹ * t⁻¹ * x)⁻¹)) =
        Fintype.card G * ι (χ t) * ι (χ h) / n₀ := by
      intro h
      rw [eq_div_iff hn0, ← hAv h t, mul_comm]
      congr 1
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp [mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, map_sum, map_mul, map_div₀, map_natCast, hn]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hx]
    calc (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) *
          ∑ h : P, ι (((ψ h)⁻¹ : Kˣ) : K) * (Fintype.card G * ι (χ t) * ι (χ h) / n₀)
        = (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) *
          (Fintype.card G * ι (χ t) / n₀ * ∑ h : P, ι (χ h) * ι (((ψ h)⁻¹ : Kˣ) : K)) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun h _ => by ring
      _ = ι (χ t) := by
          rw [hsum']
          field_simp
  let e : Module.End K (MonoidAlgebra K G) := LinearMap.mulRight K f
  have he : e * e = e := by
    refine LinearMap.ext fun x => ?_
    simp [e, mul_assoc, hidem]
  have hcomm : ∀ t, _root_.GlobalTheory.MultOneRealised.leftReg K G t * e = e * _root_.GlobalTheory.MultOneRealised.leftReg K G t := by
    intro t
    refine LinearMap.ext fun x => ?_
    simp [e, _root_.GlobalTheory.MultOneRealised.leftReg, mul_assoc]
  obtain ⟨n, τ, hτ⟩ := _root_.GlobalTheory.BI.isChar_trace_mul_idempotent K G _ (_root_.GlobalTheory.MultOneRealised.leftReg K G) e he hcomm
  have htr : ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
    intro g
    have := hτ g
    dsimp only [e] at this
    rw [trace_leftReg_mul_mulRight_eq_sum_coeff] at this
    simp only [hf, hI2, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this.symm
  have hτ1 : Module.finrank K (τ.IntertwiningMap τ) = 1 := by
    have hq := _root_.GlobalTheory.BI.pair_character_eq_finrank K (AlgebraicClosure K)
      G _ _ τ τ
    have hfun' : (fun g => algebraMap K (AlgebraicClosure K) (τ.character g)) =
        fun g => algebraMap K (AlgebraicClosure K) (χ g) := by
      funext g; rw [show τ.character g = χ g from htr g]
    rw [hfun', hp1] at hq
    exact_mod_cast hq.symm
  obtain ⟨hnt, hsurj⟩ := _root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one K G _ τ hτ1
  refine ⟨n, τ, ?_, hsurj, htr⟩
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)
  · exact h0

end GlobalTheory.MultOneRealised
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOneStatement
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  first | exact @GlobalTheory.MultOneRealised.exists_rep_of_mult_one | exact GlobalTheory.MultOneRealised.exists_rep_of_mult_one | (intros; apply GlobalTheory.MultOneRealised.exists_rep_of_mult_one <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne
noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add (f := _), mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOneStatement
open Formalism.L2.DIV NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  first | exact @GlobalTheory.GoodFamilyOfChars.exists_goodFamily | exact GlobalTheory.GoodFamilyOfChars.exists_goodFamily | (intros; apply GlobalTheory.GoodFamilyOfChars.exists_goodFamily <;> assumption)
end
end

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem passIn3_of_rows : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ), R.WeakCharacterisation F → A3.fam3.Ok3 1 → PrimRows3 R F → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (R.num F C CH).de = 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) → (R.num F C CH).la = Real.log (Fintype.card G) → PassIn3 R F C CH := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F C CH hC hOk hP hser hadm hde hla
  classical
  have hlev : R.toRealDat.grp_levels F.lv2 := hC.base.grp.levels
  have hrec : R.toRealDat.grp_record := hC.base.grp.record
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hind := GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hrec hser hirr
  letI i0 : Fintype F.P0 := Fintype.ofFinite _
  letI i1 : Fintype F.P1 := Fintype.ofFinite _
  have hone : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    @GlobalTheory.RealOneVector.typeSum_base_eq_card D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hind i0
  obtain ⟨S, iS, Ws, iA, iM, iF, τ, hgood, hchars, hm1⟩ :=
    GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne D.what₂.LL G A3.A.X hirr F.P0 F.ψ0 hone
  obtain ⟨hcard, hres⟩ := GlobalTheory.typePlaces_card_and_residue_le D G Pl0 T A3.A Ks R.toRealDat hrec
  have hcol := @GlobalTheory.ColumnMultSum.columnMult D G _ _ Pl0 T A3.A Ks _ _ _ R.toRealDat F.lv2 hlev hcard hres hadm hirr hind i1
  refine ⟨S, iS, Ws, iA, iM, iF, τ, (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ), ?_⟩
  refine ⟨GlobalTheory.ratMuP_of_rowTest D G Pl0 I0 T A3 Ks R F hP.rowTest hP.h2P, hgood, hchars, hm1, ?_, ?_, ?_⟩
  · exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos R.Pg D.R.k
  · intro s
    obtain ⟨n, hn, hb⟩ := hcol (Formalism.IndefR.TransferLatticeStatement.charOf (τ s)) ((hchars _).2 ⟨s, rfl⟩)
    have hnOf := GlobalTheory.T.multiplicity_linearCharacter_eq_characterSum D.what₂.LL G (Ws s) (τ s) F.P1 F.ψ1
    have heq : Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨F.P1, F.ψ1⟩ = n := by
      apply Nat.cast_injective (R := D.what₂.LL)
      rw [hnOf]
      exact hn
    rw [heq]
    have hde' : ((faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs).Z.num C CH).de = _ := hde
    rw [hde']
    have := abs_le.1 hb
    constructor <;> nlinarith [this.1, this.2]
  · exact hla

end GlobalTheory

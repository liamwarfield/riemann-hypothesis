module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
public import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
public import Formalism.LocalToGlobal.Columns.ChainTopLawTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Formalism.LocalToGlobal.KernelLattices.TopPin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open scoped Pointwise

namespace GlobalTheory.AboveL

theorem mem_dec_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) :
    g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := K') A := by
  have key : ((g • A : ValuationSubring Ω) : Set Ω) = ((g' • A : ValuationSubring Ω) : Set Ω) := by
    rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]
  unfold Dec
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; apply SetLike.coe_injective; rw [← key]; exact congrArg _ h
  · intro h; apply SetLike.coe_injective; rw [key]; exact congrArg _ h

theorem exists_cm_solvable_split : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  intro Ω _ E _ _ _ _ _ A w h N hN
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := Ideal.comap_ne_bot_of_integral_mem hx₀0 hx₀ (Algebra.IsIntegral.isIntegral x₀) }
  have hv : IsPlaceOver A v := by
    intro x
    show _ ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [← h]
    rfl
  obtain ⟨T, hvT, hlift⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hN

  let φ := IsScalarTower.toAlgHom F E Ω
  let K : IntermediateField F Ω := φ.fieldRange
  haveI : FiniteDimensional F K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  have hK : ∀ g : G F Ω, g ∈ K.fixingSubgroup ↔ ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x; exact hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩; exact hg x
  let V : Subgroup (Dec (F := F) A) := K.fixingSubgroup.subgroupOf (Dec (F := F) A)
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
  haveI : Fact (Nat.card (E ≃ₐ[F] E)).Prime :=
    ⟨by rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E]; exact Nat.prime_two⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card rfl
  have habel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ := fun σ τ => (IsCyclic.commGroup).mul_comm σ τ
  have hcomm : commutator (Dec (F := F) A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mem_subgroupOf, hK]
    intro x
    have h1 : AlgEquiv.restrictNormalHom (K₁ := Ω) E ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [habel (AlgEquiv.restrictNormalHom E (a : G F Ω)) (AlgEquiv.restrictNormalHom E (b : G F Ω))]
      group
    have h2 := AlgEquiv.restrictNormal_commutes ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E x
    have h3 : AlgEquiv.restrictNormal ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E = 1 := h1
    rw [← h2, h3]
    rfl
  obtain ⟨F₁, hF₁fin, hF₁ab, hF₁real, hF₁dec, hF₁T⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F A v hv V hVo hcomm T hvT
  obtain ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, hfix, hsub⟩ :=
    hlift F₁ hF₁fin inferInstance (isSolvable_of_comm fun a b => hF₁ab.toIsMulCommutative.is_comm.comm a b) hF₁real hF₁T
  have hkey : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ z ∈ F₁, g z = z) →
      ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g hg hz
    exact (hK g).1 (Subgroup.mem_subgroupOf.1 ((hF₁dec ⟨g, hg⟩).1 ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hz)))
  have hkey2 : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) →
      ∀ z ∈ F₁, g z = z := by
    intro g hg hE
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hF₁dec ⟨g, hg⟩).2 (Subgroup.mem_subgroupOf.2 ((hK g).2 hE)))
  refine ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, ?_, ?_⟩
  · intro g hg
    apply (hfix g).2
    let g' : G F Ω := g.restrictScalars F
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    exact hkey2 g' hg' (fun x => g.commutes x)
  · intro g hg
    have hfixP : ∀ x ∈ maximalRealSubfield M, g (algebraMap M Ω x) = algebraMap M Ω x :=
      fun x hx => g.commutes ⟨x, hx⟩
    have hF1 : ∀ z ∈ F₁, g z = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hsub z hz
      exact hfixP x hx
    have hFfix : ∀ y : F, g.toRingEquiv (algebraMap F Ω y) = algebraMap F Ω y :=
      fun y => hF1 _ (F₁.algebraMap_mem y)
    let g' : G F Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hFfix
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    have hE : ∀ x : E, g.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := hkey g' hg' hF1
    let g'' : G E Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hE
    exact (hfix g'').2 hF1

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlaceStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_solvable_cm_extension_split_place : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  first | exact @GlobalTheory.AboveL.exists_cm_solvable_split | exact GlobalTheory.AboveL.exists_cm_solvable_split | (intros; apply GlobalTheory.AboveL.exists_cm_solvable_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.BlockDecompositionK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem reduction_eq_zero_of_integral_absNorm_pow_inv_mul {c : ℕ} {a : E} (h : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * a)) : redP P a = 0 := by
  apply redP_eq_zero_of_div
  have hq := qOf_ne_zero (P := P)
  have h2 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul h
  convert h2 using 1
  rw [pow_succ]
  field_simp

theorem intAt_inv_of_isUnit {a : E} (ha : IntAt P a) (hu : IsUnit (redP P a)) : a ≠ 0 ∧ IntAt P a⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := id ha
  have hsp := reduction_spec P hs h
  have hr : r ∉ P.asIdeal := fun hr => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr] at hsp
    have hs0 : (Ideal.Quotient.mk P.asIdeal) s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact hs0 ((hu.mul_left_eq_zero).1 hsp)
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    intro h0
    exact hr (h0 ▸ Ideal.zero_mem _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hr0 h.symm
  refine ⟨ha0, ?_⟩
  have h1 := (IntAt.coe P s).div_of_notMem hr
  convert h1 using 1
  rw [eq_div_iff hr0, ← h]
  field_simp

theorem mulVec_mem_stdAt {n : ℕ} {M : Matrix (Fin n) (Fin n) E} (hM : ∀ i l, IntAt P (M i l)) {x : Sp E n}
    (hx : x ∈ stdAt E n P) : M.mulVec x ∈ stdAt E n P :=
  mem_stdAt.2 fun i => by
    show IntAt P (∑ l, M i l * x l)
    exact intAt_sum _ fun l _ => (hM i l).mul (mem_stdAt.1 hx l)

theorem exists_glint_of_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : ∀ i l, IntAt P (A i l))
    (hd : IsUnit (redP P A.det)) : ∃ j : GLint E n P, ∀ x, j.1 x = A.mulVec x := by
  obtain ⟨hne, hinv⟩ := intAt_inv_of_isUnit (det_int hA).1 hd
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 hne
  let I : Invertible A := Matrix.invertibleOfIsUnitDet A hU
  have hB : ∀ i l, IntAt P (A⁻¹ i l) := by
    intro i l
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine hinv.mul ?_
    rw [Matrix.adjugate_apply]
    refine (det_int fun a b => ?_).1
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    · exact hA a b
  have hf : ∀ x, Matrix.toLinearEquiv' A I x = A.mulVec x := fun x => rfl
  have hf' : ∀ x, (Matrix.toLinearEquiv' A I).symm x = A⁻¹.mulVec x := fun x => by
    rw [← Matrix.invOf_eq_nonsing_inv]
    rfl
  refine ⟨⟨Matrix.toLinearEquiv' A I, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩, hf⟩
  · have := mulVec_mem_stdAt hB h
    rwa [← hf', LinearEquiv.symm_apply_apply] at this
  · rw [hf]
    exact mulVec_mem_stdAt hA h

theorem inv_extI_mul_mem {N n : ℕ} (hN : N = n + 1) (c : ℕ) (g : GLint E N P) (j : GLint E n P)
    (hj : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC hN l) 1) (Br.iC hN i))
    (hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iL hN) 1) (Br.iC hN i)))
    (hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iC hN l) 1) (Br.iL hN)))
    (hD : IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Br.iL hN) 1) (Br.iL hN) - 1))) :
    (extI hN P j)⁻¹ * g ∈ prinCong N P c := by
  subst hN
  rw [inv_mul_mem_prinCong]
  intro x hx
  have hxi := mem_stdAt.1 hx
  have eg : ∀ i, g.1 x i = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i +
      x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) i := fun i => by
    have := apply_eq_sum (g.1 : Sp E (n + 1) →ₗ[E] Sp E (n + 1)) x i
    rw [Fin.sum_univ_castSucc] at this
    exact this
  refine mem_stdAt.2 fun k => ?_
  show IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 x k - (extI rfl P j).1 x k))
  rw [extI_val]
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have e : sumE rfl j.1 1 x (Fin.last n) = x (Fin.last n) := by
      have := sumE_last (rfl : n + 1 = n + 1) j.1 1 x
      rw [Units.val_one, one_mul] at this
      exact this
    rw [e, eg]
    have e2 : ((qOf P : E) ^ c)⁻¹ * (∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) +
        x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - x (Fin.last n)) =
        ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) +
        x (Fin.last n) * (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - 1)) := by
      rw [show ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) =
          ((qOf P : E) ^ c)⁻¹ * ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring]
      ring
    rw [e2]
    exact IntAt.add (intAt_sum _ fun l _ => (hxi _).mul (hC l)) ((hxi _).mul hD)
  · have e : sumE rfl j.1 1 x i.castSucc = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i.castSucc := by
      have h1 := congrFun (prH_sumE (rfl : n + 1 = n + 1) j.1 1 x) i
      rw [prH_apply] at h1
      have h2 := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) (prH E rfl x) i
      rw [LinearEquiv.coe_coe] at h2
      rw [show i.castSucc = Br.iC (rfl : n + 1 = n + 1) i from rfl, h1, h2]
      exact Finset.sum_congr rfl fun l _ => by rw [prH_apply, hj]; rfl
    rw [e, eg, add_sub_cancel_left, mul_left_comm]
    exact (hxi _).mul (hB i)

theorem det_last {κ : Type} [CommRing κ] {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (h0 : ∀ l : Fin n, R (Fin.last n) l.castSucc = 0) (h1 : R (Fin.last n) (Fin.last n) = 1) :
    R.det = (R.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row R (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, h1, mul_one, Fin.succAbove_last, Fin.val_last]
  rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]

theorem coarse_two {r b n : ℕ} (hn : n = r + b) (k : Fin n) : coarse r [b] k.1 = if k.1 < r then 0 else 1 := by
  split_ifs with h
  · exact coarse_of_lt h
  · rw [coarse_of_le (Nat.not_lt.1 h)]
    simp only [blkIdx]
    rw [if_pos (by have := k.2; omega)]

theorem exists_block_of_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  intro E _ _ _ P N n hN r b c hn g hg
  subst hN
  obtain ⟨-, hT1, hT2⟩ := isKOneType_of_mem_kOne P g hg
  have eC : ∀ l : Fin n, Br.iC (rfl : n + 1 = n + 1) l = l.castSucc := fun l => rfl
  have eL : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have hlast : (Fin.last n).1 + 1 = n + 1 := by simp
  have hC' : ∀ i : Fin n, ¬ (i.castSucc : Fin (n + 1)).1 + 1 = n + 1 := fun i h => by
    simp only [Fin.coe_castSucc] at h; omega
  have hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iL rfl) 1) (Br.iC rfl i)) :=
    fun i => hT1 _ _ (iff_of_false (hC' i) (not_not.2 hlast))
  have hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iC rfl l) 1) (Br.iL rfl)) :=
    fun l => hT1 _ _ (iff_of_true hlast (hC' l))
  have hD : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * (g.1 (Pi.single (Br.iL rfl) 1) (Br.iL rfl) - 1)) := hT2 _ hlast
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun i l => g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i)
  have hAint : ∀ i l, IntAt P (A i l) := fun i l => glint_entry g _ _
  have hdet : IsUnit (redP P A.det) := by
    rw [redP_det A hAint]
    have hR := IsUnit.map Matrix.detMonoidHom (Units.isUnit (redGL (n + 1) P g))
    have e1 : A.map (redP P) = (redMat g).submatrix Fin.castSucc Fin.castSucc := by
      ext i l
      rfl
    rw [e1, ← det_last]
    · exact hR
    · intro l
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (hC l)
    · have h := reduction_eq_zero_of_integral_absNorm_pow_inv_mul hD
      rw [reduction_sub (glint_entry g _ _) intAt_one, reduction_one₂, sub_eq_zero] at h
      exact h
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hAint hdet
  have hj' : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i) := fun i l => by
    rw [hj]
    simp [Matrix.mulVec_single_one, A]
  refine ⟨j, ?_, inv_extI_mul_mem rfl (c + 1) g j hj' hB hC hD⟩
  show redGL n P j ∈ btG n _ (coarse r [b])
  rw [mem_btG]
  intro i l hil
  rw [coarse_two hn, coarse_two hn] at hil
  have hl : l.1 < r := by
    by_contra h
    rw [if_neg h] at hil
    split_ifs at hil <;> omega
  have hi : r ≤ i.1 := by
    by_contra h
    rw [if_pos (Nat.lt_of_not_le h)] at hil
    omega
  rw [redGL_val]
  show redP P (j.1 (Pi.single l 1) i) = 0
  rw [hj']
  have hv : (Pi.single (Br.iC rfl l) 1 : Sp E (n + 1 + 0)) ∈ LocE.parL P (qOf P) r (n + 1) 0 :=
    GlobalTheory.LastSteps.mem_sclLat.2 fun k => by
      by_cases hk : k = Br.iC rfl l
      · subst hk
        have : ¬ (r ≤ (Br.iC (rfl : n + 1 = n + 1) l).1 ∧ (Br.iC (rfl : n + 1 = n + 1) l).1 < n + 1) := fun h => by
          have := h.1; simp [Br.iC] at this; omega
        simp only [if_neg this, zpow_zero, inv_one, one_mul, Pi.single_eq_same]
        exact intAt_one
      · simp only [Pi.single_apply, hk, if_false, mul_zero]
        exact intAt_zero
  have h1 := GlobalTheory.LastSteps.mem_sclLat.1 (((hg.1.2 _).2 hv)) (Br.iC rfl i)
  have h2 : r ≤ (Br.iC (rfl : n + 1 = n + 1) i).1 ∧ (Br.iC (rfl : n + 1 = n + 1) i).1 < n + 1 := by
    simp [Br.iC]; omega
  rw [if_pos h2, zpow_one] at h1
  apply redP_eq_zero_of_div
  rw [div_eq_inv_mul]
  exact h1

end GlobalTheory.BlockDecompositionK1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecompositionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_k1_block_decomposition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  first | exact @GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | exact GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | (intros; apply GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalar
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.LocOpAct

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cosetSum_mem_fixed (ρ : Representation ℂ G V) {K N : Subgroup G} [Fintype (K ⧸ N.subgroupOf K)] {v : V}
    (hv : v ∈ GroundTheory.Automorphic.fixedVectors ρ N) :
    GroundTheory.Automorphic.cosetSum ρ K N v ∈ GroundTheory.Automorphic.fixedVectors ρ K := by
  intro k hk
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GroundTheory.Automorphic.cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := GroundTheory.Automorphic.act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out ((⟨k, hk⟩ : K) • q)) (by
      rw [QuotientGroup.out_eq']; conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl)
  simpa using this

theorem opOf_eq (ρ : Representation ℂ G V) (f : G →₀ ℂ) (v : V) :
    GlobalTheory.Cong.opOf ρ f v = (f.sum fun g c => c • ρ g) v := by
  simp [GlobalTheory.Cong.opOf, Finsupp.sum, LinearMap.sum_apply]

theorem opOf_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (F : V →ₗ[ℂ] W) (hF : ∀ g v, F (ρ g v) = τ g (F v)) (f : G →₀ ℂ) (v : V) :
    F (GlobalTheory.Cong.opOf ρ f v) = GlobalTheory.Cong.opOf τ f (F v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.Cong.opOf, Finsupp.sum, map_sum, map_smul, hF]

end GlobalTheory.LocOpAct

theorem GlobalTheory.Cong.opOf_locU_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  classical
  intro E _ _ _ a w hw Kw hKc hKo f z hf
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw
  let e : locU a w ≃* GL (Fin a) (w.adicCompletion E) :=
    MulEquiv.ofBijective ((cLoc w).comp (locU a w).subtype) hbij
  let j : GL (Fin a) (w.adicCompletion E) →* UA E a := (locU a w).subtype.comp e.symm.toMonoidHom
  let ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (UA E a → ℂ) := (RU E a).comp j
  have hcj : ∀ g, cLoc w (j g) = g := fun g => e.apply_symm_apply g
  have hinj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  haveI : CompactSpace Kw := isCompact_iff_compactSpace.1 hKc
  have hfin : ∀ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) →
      Finite (Kw ⧸ N.subgroupOf Kw) := fun N hN =>
    Subgroup.quotient_finite_of_isOpen _ (by rw [Subgroup.coe_subgroupOf]; exact hN.preimage continuous_subtype_val)
  refine ⟨f.mapDomain j, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact ⟨(e.symm h).2, by rw [Finsupp.mapDomain_apply_of_injective hinj, hcj]⟩
  · intro U hU σ hσ φ hφU hφK
    have hop : ∀ ψ, opOf (RU E a) (f.mapDomain j) ψ = opOf ρ' f ψ := by
      intro ψ
      simp only [GlobalTheory.Cong.opOf]
      rw [Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b c₁ c₂; simp [add_smul])]
      rfl
    rw [hop]
    have hFint : ∀ (F : {F : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, F v ∈ U) ∧
        ∀ (x : locU a w) v, F (σ.ρ (cLoc w x) v) = RU E a x (F v)}) g v, F.1 (σ.ρ g v) = ρ' g (F.1 v) := by
      intro F g v
      have h := F.2.2 (e.symm g) v
      have h2 : cLoc w ((e.symm g : locU a w) : UA E a) = g := hcj g
      rw [h2] at h
      exact h
    let T : Module.End ℂ (UA E a → ℂ) := (f.sum fun g c => c • ρ' g) - z σ • 1
    have hT : ∀ ψ, T ψ = opOf ρ' f ψ - z σ • ψ := fun ψ => by
      rw [GlobalTheory.LocOpAct.opOf_eq]; rfl
    have key := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hσ φ hφU
    have hC : ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' φ) = 0 := by
      refine Submodule.iSup_induction _ (motive := fun ψ => ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)),
        IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' ψ) = 0) key ?_ ?_ ?_
      · rintro F _ ⟨v, rfl⟩
        refine ⟨GroundTheory.Automorphic.stabilizerOf σ.ρ v, σ.smooth v, fun N' hN' hle => ?_⟩
        haveI := hfin N' hN'
        haveI := Fintype.ofFinite (Kw ⧸ N'.subgroupOf Kw)
        have hv : v ∈ GroundTheory.Automorphic.fixedVectors σ.ρ N' := fun n hn => hle hn
        have hu := GlobalTheory.LocOpAct.cosetSum_mem_fixed σ.ρ (K := Kw) hv
        have hcs : GroundTheory.Automorphic.cosetSum ρ' Kw N' (F.1 v) = F.1 (GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [GroundTheory.Automorphic.cosetSum_apply, GroundTheory.Automorphic.cosetSum_apply, map_sum]
          simp only [hFint]
        have hfix : GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v ∈ GlobalTheory.PRep.fixed σ.ρ Kw := fun k => by
          show σ.ρ k _ = ((1 : Kw →* ℂˣ) k : ℂ) • _
          simp [hu k k.2]
        rw [hcs, hT, ← GlobalTheory.LocOpAct.opOf_map σ.ρ ρ' F.1 (hFint F) f, hf σ _ hfix, map_smul, sub_self]
      · exact ⟨⊤, by simp, fun N' _ _ => by simp⟩
      · rintro x y ⟨N₁, h₁, hx⟩ ⟨N₂, h₂, hy⟩
        refine ⟨N₁ ⊓ N₂, by rw [Subgroup.coe_inf]; exact h₁.inter h₂, fun N' hN' hle => ?_⟩
        rw [map_add (f := _), map_add (f := _), hx N' hN' (hle.trans inf_le_left), hy N' hN' (hle.trans inf_le_right), add_zero]
    obtain ⟨N, hN, hNφ⟩ := hC
    haveI := hfin N hN
    haveI := Fintype.ofFinite (Kw ⧸ N.subgroupOf Kw)
    have hφ : φ ∈ GroundTheory.Automorphic.fixedVectors ρ' Kw := fun k hk => by
      have := hφK (j k) (e.symm k).2 (by rw [hcj]; exact hk)
      exact this
    have h0 := hNφ N hN le_rfl
    rw [GroundTheory.Automorphic.cosetSum_of_mem ρ' hφ, map_smul] at h0
    have hne : (Fintype.card (Kw ⧸ N.subgroupOf Kw) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [smul_eq_zero] at h0
    have h1 := h0.resolve_left hne
    rw [hT, sub_eq_zero] at h1
    exact h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalOperatorActsByLocalComponentScalarStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
theorem _root_.GlobalTheory.T.localOperator_acts_by_localComponentScalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  first | exact @GlobalTheory.Cong.opOf_locU_eq_smul | exact GlobalTheory.Cong.opOf_locU_eq_smul | (intros; apply GlobalTheory.Cong.opOf_locU_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host

namespace GlobalTheory.HeckeUnrExt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)

theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

def lev (K : Type) [Field K] [NumberField K] (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v⟩

theorem lev_mem_nhds (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) :
    (lev K N : Set (Ideles K)) ∈ nhds (1 : Ideles K) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Ideles K => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Ideles K => (x⁻¹).val.2 := h1.comp continuous_inv
  have h3 : Continuous fun x : Ideles K =>
      (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹ :=
    (h1.sub continuous_const).mul continuous_const
  have hU := ((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_
  · have : ((1 : Ideles K).val.2 - 1) = 0 := sub_self _
    simp only [this, zero_mul]
    exact zero_mem _
  · rintro y ⟨⟨hy, hy'⟩, hy''⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
        congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
    · have e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1 := hy'' v
      haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
      have h0 : Valued.v (N : v.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.2 hN
      rw [map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul] at e
      exact e

noncomputable def crd (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  Units.map ((InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))).toMonoidHom

noncomputable def kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Ideles K →* ℂˣ :=
  ∏ w : InfinitePlace K, crd K w ^ a

theorem coe_kap (K : Type) [Field K] [NumberField K] (a : ℤ) (x : Ideles K) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w (x.val.1 w) ^ a := by
  rw [kap, MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
  rfl

theorem continuous_kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Continuous (kap K a) := by
  have e : (kap K a : Ideles K → ℂˣ) = fun x => ∏ w : InfinitePlace K, (crd K w x) ^ a := by
    funext x
    rw [kap, MonoidHom.finsetProd_apply]
    rfl
  rw [e]
  refine continuous_finsetProd _ fun w _ => Continuous.zpow (f := crd K w) (Continuous.units_map _ ?_) a
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem coe_infDiag' {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    (infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem kap_of_fst {K : Type} [Field K] [NumberField K] (a : ℤ) (x : Ideles K) (k : K)
    (h : x.val.1 = algebraMap K (InfiniteAdeleRing K) k) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, w.embedding k ^ a := by
  rw [coe_kap, h]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [InfiniteAdeleRing.algebraMap_apply]
  simpa using InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)

theorem dense_inf (F : Type) [Field F] [NumberField F] :
    DenseRange (Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) :=
    Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace F, v.Completion)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ :=
    (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact v.ne_zero hk
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem bij_emb (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Bijective fun w : InfinitePlace E => w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  constructor
  · intro w w' h
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, ← InfinitePlace.mk_embedding w,
      ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk]
    exact congrArg _ h
  · intro φ
    refine ⟨InfinitePlace.mk (ComplexEmbedding.lift E φ), ?_⟩
    rcases InfinitePlace.embedding_mk_eq (ComplexEmbedding.lift E φ) with h | h
    · simp only [h, ComplexEmbedding.lift_comp_algebraMap]
    · simp only [h]
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.lift_comp_algebraMap]
      exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal φ)

theorem psi_eq_kap (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E))
    (a : ℤ) (hψ : ψ.IsAlg fun _ => a) (z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ) :
    ψ.1 (Units.map (MonoidHom.inl _ _) z) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
  have c2 : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing (maximalRealSubfield E))
      (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (dense_inf _).induction_on z (isClosed_eq (ψ.2.1.comp c2)
    ((continuous_kap E a).comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E).comp c2))) fun k => ?_
  apply Units.ext
  rw [kap_of_fst a _ (algebraMap _ E (k : maximalRealSubfield E))
    (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap _ E (k : maximalRealSubfield E)))]
  refine Eq.trans ?_ ((hψ k).trans ?_)
  · exact congrArg (fun x => ((ψ.1 x : ℂˣ) : ℂ)) (Units.ext (coe_infDiag' k).symm)
  · exact ((bij_emb E).prod_comp fun φ => φ (k : maximalRealSubfield E) ^ a).symm

open Classical in
theorem prod_type (E : Type) [Field E] [NumberField E] (a : ℤ) (k : E) :
    ∏ w : InfinitePlace E, w.embedding k ^ a =
      ∏ φ : E →+* ℂ, φ k ^ (if (InfinitePlace.mk φ).embedding = φ then a else 0) := by
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_single_of_mem w.embedding (by simp)]
  · rw [InfinitePlace.mk_embedding, if_pos rfl]
  · intro φ hφ hne
    rw [(Finset.mem_filter.1 hφ).2, if_neg hne.symm, zpow_zero]

def levT (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v ∈ T,
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v _ => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v hv => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v hv)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v hv⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v hv => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v hv⟩

theorem lev_le_levT (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    lev K N ≤ levT K T N := fun _ ha => ⟨ha.1, fun v _ => ha.2 v⟩

theorem levT_mem_nhds (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) {N : ℕ} (hN : N ≠ 0) :
    (levT K T N : Set (Ideles K)) ∈ nhds (1 : Ideles K) :=
  Filter.mem_of_superset (lev_mem_nhds K hN) (lev_le_levT K T N)

theorem levT_anti (K : Type) [Field K] [NumberField K] {T T' : Set (HeightOneSpectrum (𝓞 K))} (h : T' ⊆ T) (N : ℕ) :
    levT K T N ≤ levT K T' N := fun _ ha => ⟨ha.1, fun v hv => ha.2 v (h hv)⟩

end GlobalTheory.HeckeUnrExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem xiOver_eq_XiTopG {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl

theorem xiOver_eq_XiTop : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  intro X Pr R Ch sel S mu cst u n h p Y p'
  exact xiOver_eq_XiTopG Ch sel mu cst n h p Y p'

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  first | exact @GlobalTheory.Mem.Col2.xiOver_eq_XiTop | exact GlobalTheory.Mem.Col2.xiOver_eq_XiTop | (intros; apply GlobalTheory.Mem.Col2.xiOver_eq_XiTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.TopInt

open GlobalTheory.PhiRootVal (RootOrZero phiGS_root phiG_root phiQ_root)
open GlobalTheory.CplTwoInt (intOff_prod ftY_intOff smul_symm_mem repY_mem)

theorem phiTopG_root {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (sharp : Bool) (i j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTopG (R := R) Ch mu sharp i j n P x) := by
  unfold PhiTopG
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem xiTop_intOff (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (u) (μ)
    (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (Yb : Set (Sp t.X.E (D.R.N i)))
    (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)) (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1)))
    (hY : Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  have hok := t.idx_ok μ
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem topInt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  intro D L hT Gi Gl K Y cX ex t hTop u μ c c' _ x
  obtain ⟨-, -, pt, ix, yb, pT, -, hyb, -, -, hpin, -, -⟩ := hTop u μ
  rw [hpin.2 c c' x]
  exact xiTop_intOff D L hT Gi Gl K Y cX ex t u μ _ _ _ _ _ (hyb c)

end GlobalTheory.TopInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepKernelData_integral_awayFromLevels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  first | exact @GlobalTheory.TopInt.topInt | exact GlobalTheory.TopInt.topInt | (intros; apply GlobalTheory.TopInt.topInt <;> assumption)
end
end

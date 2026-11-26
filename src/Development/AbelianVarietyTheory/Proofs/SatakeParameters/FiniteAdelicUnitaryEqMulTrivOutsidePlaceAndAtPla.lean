module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPla
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPla
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceDecomp

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n),
    ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  intro L _ _ _ n v κ
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L v 1 * GlobalTheory.InertUmax.sgl L v 1 = GlobalTheory.InertUmax.sgl L v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L v 1 w * GlobalTheory.InertUmax.sgl L v 1 w = GlobalTheory.InertUmax.sgl L v 1 w
    rcases eq_or_ne w v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have hcv : compAt L v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ v → compAt L w e = 0 := fun w hw => by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]
  let θ : AL L × AL L →+* AL L :=
    { toFun := fun q => e * q.1 + (1 - e) * q.2
      map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring
      map_mul' := fun q q' => by
        simp only [Prod.fst_mul, Prod.snd_mul]
        linear_combination (-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2
      map_zero' := by simp
      map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }
  have hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2 := fun _ => rfl
  have hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b) := by
    intro a b; rw [hθ, hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hce]
  have hθv : ∀ q, compAt L v (θ q) = compAt L v q.1 := by
    intro q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L) :=
    fun A B => (pr A B).map θ
  have hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j := fun _ _ _ _ => rfl
  have M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D) := by
    intro A B C D; show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ
    rw [← Matrix.map_mul, pr_mul]
  have M_one : M 1 1 = 1 := by
    show (pr 1 1).map θ = 1
    rw [pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B) := by
    intro A B; ext i j
    show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))
    exact hθc _ _
  have M_diag : ∀ A, M A A = A := by intro A; ext i j; rw [hM]; ring
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    show compAt L w (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.PlaceDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPlaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n), ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  first | exact @GlobalTheory.PlaceDecomp.decomp | exact GlobalTheory.PlaceDecomp.decomp | (intros; apply GlobalTheory.PlaceDecomp.decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEigenvector
namespace GlobalTheory.ExistsEigenvector

theorem exists_eigenvector {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {U : Set G} (hU : IsOpen U)
    (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθ : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hne : ∑ i, T i (y i) ≠ 0) (heq : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v := by
  classical
  have hone : θ 1 = 1 := hθ 1 h1 K.one_mem
  have hθne : ∀ a ∈ K, θ a ≠ 0 := fun a ha h0 => by
    have := hmul a ha a⁻¹ (K.inv_mem ha)
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup K :=
    { carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, fun i => ?_⟩
        · rw [Subgroup.coe_mul, hmul _ a.2 _ b.2, ha, hb, one_mul]
        · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := ⟨hone, fun i => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, fun i => ?_⟩
        · have := hmul _ a.2 _ (K.inv_mem a.2)
          rw [mul_inv_cancel, hone, ha, one_mul] at this
          exact this.symm
        · conv_lhs => rw [← ha' i]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
  have hHo : IsOpen (H : Set K) := by
    have ho : IsOpen ((fun k : K => (k : G)) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      (hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))).preimage continuous_subtype_val
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨h1, by simp⟩) ?_)
    rintro k ⟨hk, hk'⟩
    exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : K → ι → V := fun k i => (θ k)⁻¹ • ρ k (y i)
  have hf : ∀ a b : K, QuotientGroup.leftRel H a b → f a = f b := by
    intro a b hab
    obtain ⟨h, h'⟩ : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have e : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
    funext i
    simp only [f]
    rw [e, hmul _ a.2 _ (a⁻¹ * b).2, h, mul_one, map_mul, Module.End.mul_apply, h']
  let F : K ⧸ H → ι → V := fun q => Quotient.liftOn' q f hf
  have hF : ∀ (h : K) (q : K ⧸ H) (i : ι), ρ h (F q i) = θ h • F (h • q) i := by
    intro h q i
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ρ h ((θ k)⁻¹ • ρ k (y i)) = θ h • ((θ (h * k))⁻¹ • ρ (h * k) (y i))
      rw [hmul _ h.2 _ k.2, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_inv,
        mul_inv_cancel_left₀ (hθne _ h.2)]
  have hT : ∀ q : K ⧸ H, ∑ i, T i (F q i) = ∑ i, T i (y i) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ∑ i, T i ((θ k)⁻¹ • ρ k (y i)) = _
      simp only [map_smul]
      rw [← Finset.smul_sum, heq _ k.2, smul_smul, inv_mul_cancel₀ (hθne _ k.2), one_smul]
  have hex : ∃ i, ∑ q, F q i ≠ 0 := by
    by_contra hc
    have hc' : ∀ i, ∑ q, F q i = 0 := fun i => not_not.1 fun h => hc ⟨i, h⟩
    have h0 : ∑ i, T i (∑ q, F q i) = 0 := by simp [hc']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [hT] at h0
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 h0)
    · exact hne h0
  obtain ⟨i, hi⟩ := hex
  refine ⟨_, hi, fun h hh => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun q _ => hF ⟨h, hh⟩ q i]
  exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (fun q : K ⧸ H => θ h • F q i)

end GlobalTheory.ExistsEigenvector
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocal

open GlobalTheory.PRep

theorem exists_trivOutside_map_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (h : GL (Fin n) (s.w.adicCompletion L)) :
    ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h := by
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  refine ⟨x, hx, ?_⟩
  rw [e]
  ext i j
  simp

theorem exists_eigen_of_sum {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V) (hf0 : ∑ i, T i (y i) ≠ 0)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v :=
  _root_.GlobalTheory.ExistsEigenvector.exists_eigenvector hρ hK hU h1 θ hθU hmul T y hf0 hinv

set_option maxHeartbeats 1000000 in
theorem exists_eigen_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ hK hKOne f hf hf0 hθ
  classical
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono (fun h hh => (hKOne h hh).1) GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  refine exists_eigen_of_sum σ.smooth hKc GlobalTheory.StepData.isOpen_KOne (one_mem _) θ
    (fun g hg _ => (hKOne g hg).2) hmul (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)))
    (fun j => y j.1) (by rw [hsum]; exact hf0) ?_
  intro k hk
  obtain ⟨x, hx, e, hfx⟩ := hrt k hk
  subst e
  have hj : ∀ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
      (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (y j.1)) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1)) := fun j => j.1.2.2 x hx (y j.1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl fun j _ => hj j, ← map_sum, hsum, hfx]

end GlobalTheory.EigLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_irreducible_fixed_vectors : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  first | exact @GlobalTheory.EigLocal.exists_eigen_local | exact GlobalTheory.EigLocal.exists_eigen_local | (intros; apply GlobalTheory.EigLocal.exists_eigen_local <;> assumption)
end
end

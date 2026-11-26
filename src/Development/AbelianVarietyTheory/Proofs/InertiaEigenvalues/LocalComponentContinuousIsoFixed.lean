module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPla
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenFamily
namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_smul, map_sum, smul_comm]
      apply congrArg ((Fintype.card (K ⧸ H) : ℂ)⁻¹ • ·)
      rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
      exact congrArg (θ h • ·) (Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j))
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Finset.sum_apply]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocalSum

open GlobalTheory.PRep

theorem exists_eigen_family {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ u : ι → V, (∀ j, ∀ h ∈ K, ρ h (u j) = θ h • u j) ∧ ∑ i, T i (u i) = ∑ i, T i (y i) := by
  first
  | exact @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | (apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family ..)


set_option maxHeartbeats 1000000 in
theorem exists_eigen_local_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ U hK hKOne hU hU1 hθU f hf hθ ι _ xs z hxs hz
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hz
    simp
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := GlobalTheory.EigLocal.exists_trivOutside_map_loc n s c h
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
    Subgroup.isOpen_mono hKOne GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  have hint : ∀ (j : F.support) (x : GAf L n), TrivOutside {s.v} x → ∀ v,
      (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
        (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) v) := fun j x hx v => j.1.2.2 x hx v
  obtain ⟨u, hu, hus⟩ := exists_eigen_family σ.smooth hKc hU hU1 θ hθU hmul
    (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))) (fun j => y j.1) (by
      intro k hk
      obtain ⟨x, hx, e, hfx⟩ := hrt k hk
      subst e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun j _ => hint j x hx (y j.1), ← map_sum, hsum, hfx])
  rw [hsum] at hus
  by_contra hall
  push_neg at hall
  apply hz
  have key : ∀ j, ∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j) = 0 := by
    intro j
    by_contra hne
    exact hne (hall (u j) (hu j))
  calc ∑ m, z m • NG.rt L n (xs m) f
      = ∑ m, z m • ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hus, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hint j (xs m) (hxs m) (u j)).symm
    _ = ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [key j, map_zero]

end GlobalTheory.EigLocalSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_continuous_iso_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  first | exact @GlobalTheory.EigLocalSum.exists_eigen_local_sum | exact GlobalTheory.EigLocalSum.exists_eigen_local_sum | (intros; apply GlobalTheory.EigLocalSum.exists_eigen_local_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
noncomputable section

namespace GlobalTheory.CoverOnto

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie


set_option maxHeartbeats 1000000 in
theorem frBor_of_isometry {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (hr : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ) (hA : l.A = 1) {k k' : Fin F.n}
    (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    {P : (F.Di k).La →+ (Fin g → ℂ)} {P' : (F.Di k').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P) (hP' : IsPeriod (F.Di k') (fun j => relab c σ (e j).1) P')
    (h : ∀ a, P' (gam a) = P a) (y y' : FrPt Xo c (CAt σ)) (hy : y.x = F.u k P) (hy' : y'.x = F.u k' P')
    (hu : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i))
    (hu' : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) :
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y y' := by
  classical
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  have hpt := point_eq_of_isometry F hr hσ hty hA gam hEF hM hP hP' h
  obtain rfl := F.disj k k' P P' hP hP' hpt
  obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : ∀ b ∈ Mfr l • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ x, gam b = b + l.M • x := by
    intro b hb
    refine Submodule.smul_induction_on hb (fun s hs b _ => ?_) ?_
    · obtain ⟨a, d, rfl⟩ := F.t_surj k b
      obtain ⟨x, hx⟩ := hM (s • a) (Submodule.smul_mem_smul hs Submodule.mem_top)
      refine ⟨x + m • (gam (s • d) - s • d), ?_⟩
      rw [smul_add, ← map_smul, map_add (f := _), hx, smul_comm s l.M' d, map_nsmul, hm, smul_add, ← mul_smul, smul_sub]
      abel
    · rintro a b ⟨x, hx⟩ ⟨z, hz⟩
      exact ⟨x + z, by rw [map_add (f := _), hx, hz, smul_add]; abel⟩
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P' gam 1 hP hP' hEF hM'
    (fun a => ⟨gam a - a, by rw [hA, one_smul, add_sub_cancel]⟩) (fun a => by rw [Matrix.one_mulVec, h])
  simp only [Matrix.one_mulVec] at hex
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) y y' y').2.1 (hy'.trans (hpt.symm.trans hy.symm)) fun τ i =>
    ⟨(Pi.single i (1 : ℂ) : Fin (Dw.mult τ) → ℂ), ?_, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩
  · rw [Pi.single_eq_same]
    exact isUnit_one (M := ℂ)
  · rw [hy]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ) _ (y'.u τ i)).2 ?_
    have d := hu' τ i
    simp only [hex] at d
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same,
      one_smul]
    exact d


set_option maxHeartbeats 1000000 in
theorem exists_dict_comp {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (k : U.Comp) : ∃ h, (dict h).1 = k := by
  subst hr
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨x, hxd⟩ := GlobalTheory.Member.onto_dom_nonempty (U.X k)
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, -, ho, -⟩ := h1 x hxd
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', hd'⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  obtain ⟨_, -, _, -, hk⟩ := (hU.2.2.2.1 k (dict (a * f)).1 ⟨x₁, hx₁d⟩ ⟨_, hdom _⟩).1
    (frBor_of_isometry e F hpq hσ hA gam e₁ t₁ hP hP' (fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
        (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
      rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
        (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
      rfl) _ _ hy hy' hd hd')
  exact congrArg Sigma.fst hk


open GlobalTheory.CoverRead GlobalTheory.Member in
theorem exists_dict₂_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨-, hA, hinc, hU, hdom, hr, g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  exact exists_dict_comp _ hr C.U₂ C.dict₂ _ e F ik φ th _ hσ₂ hA (by omega) hU hW hD hio hth hx₀ hdom k₂

end GlobalTheory.CoverOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponentStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coverDictionary_adelic_element_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  first | exact @GlobalTheory.CoverOnto.exists_dict₂_comp | exact GlobalTheory.CoverOnto.exists_dict₂_comp | (intros; apply GlobalTheory.CoverOnto.exists_dict₂_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.DeltaExtremal

noncomputable def lead {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  if h : k ≤ n then (y.submatrix (Fin.castLE h) (Fin.castLE h)).det else 1

theorem lead_zero {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y 0 = 1 := by
  simp [lead]

theorem lead_self {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y n = y.det := by
  simp [lead]

theorem det_inv_rev {n k : ℕ} (hk : k ≤ n) (y : GL (Fin n) ℂ) :
    (Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b))).det =
      lead y.val (n - k) * (y.val.det)⁻¹ := by
  obtain ⟨e, hl, hr⟩ := GlobalTheory.ValCmp.exists_equiv_castLE_rev hk
  have hj := GlobalTheory.ValCmp.jacobi_blocks_of_mul (y.val.submatrix e e) ((y⁻¹).val.submatrix e e) 1 (by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, one_smul, Matrix.submatrix_one_equiv])
  have e1 : (y.val.submatrix e e).toBlocks₁₁ =
      y.val.submatrix (Fin.castLE (Nat.sub_le n k)) (Fin.castLE (Nat.sub_le n k)) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hl]
  have e2 : ((y⁻¹).val.submatrix e e).toBlocks₂₂ =
      Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b)) := by
    ext a b
    simp only [Matrix.toBlocks₂₂, hr, Matrix.of_apply, Matrix.submatrix_apply]
  rw [e1, e2, one_pow, one_mul, Matrix.det_submatrix_equiv_self] at hj
  rw [← hj, lead, dif_pos (Nat.sub_le n k), Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

variable {D : D7} {m n : ℕ}

theorem aeval_minorPlus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hk : k ≤ p τ) (hm : k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorPlus τ k : PolF D m n) = lead (y τ).val k := by
  rw [minorPlus, AlgHom.map_det, lead, dif_pos hn]
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  have h1 : b.val < m ∧ a.val < n := ⟨by omega, by omega⟩
  have h2 : b.val < p τ := by omega
  have h3 : b.val < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_pos h2, dif_pos h3, Matrix.submatrix_apply]
  rfl

theorem aeval_minorMinus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hm : p τ + k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorMinus τ (p τ) k : PolF D m n) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℂ) * (lead (y τ).val (n - k) * ((y τ).val.det)⁻¹) := by
  rw [minorMinus, AlgHom.map_det, ← det_inv_rev hn, ← Matrix.det_permute', ← Matrix.det_transpose]
  congr 1
  ext b a
  have ha := a.isLt
  have hb := b.isLt
  have h1 : p τ + b.val < m ∧ n - k + a.val < n := ⟨by omega, by omega⟩
  have h2 : ¬ p τ + b.val < p τ := by omega
  have h3 : p τ + b.val - p τ < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_neg h2, dif_pos h3, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  refine congrArg₂ _ (congrArg Fin.rev (Fin.ext ?_)) (Fin.ext ?_)
  · simp
  · simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castLE]
    omega

theorem sum_drops (q : ℕ) (a : ℕ → ℕ) (h : ∀ i, i + 1 < q → a (i + 1) ≤ a i) :
    ∑ i ∈ Finset.range q, (a i - if i + 1 < q then a (i + 1) else 0) = if 0 < q then a 0 else 0 := by
  have := Finset.sum_range_sub' (fun i => if i < q then (a i : ℤ) else 0) q
  simp only [lt_irrefl, if_false, sub_zero] at this
  refine Nat.cast_injective (R := ℤ) ?_
  rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have := h i
  split_ifs <;> omega

theorem prod_exponents {n p q : ℕ} (ap am : ℕ → ℕ) (c : ℤ) (lam : DomWeight n) (hle : p + q ≤ n)
    (hl : ∀ i : Fin n, lam.w i = (if i.val < p then (ap i : ℤ) else if n - q ≤ i.val then -(am (n - 1 - i) : ℤ) else 0) + c)
    (L : ℕ → ℂ) (h0 : L 0 = 1) (hd : L n ≠ 0) :
    L n ^ c * ((∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
      ∏ i ∈ Finset.range q, (L (n - (i + 1)) * (L n)⁻¹) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
    L n ^ lam.detShift * ∏ s : Fin n, L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) := by
  rcases n with _ | k
  · obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    simp [h0]
  have hanti : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i ≤ j → lam.w ⟨j, hj⟩ ≤ lam.w ⟨i, hi⟩ :=
    fun i j hi hj h => lam.anti (show (⟨i, hi⟩ : Fin (k + 1)) ≤ ⟨j, hj⟩ from h)
  have ham : ∀ i, i + 1 < q → am (i + 1) ≤ am i := by
    intro i hi
    have := hanti (k - (i + 1)) (k - i) (by omega) (by omega) (by omega)
    rw [hl, hl] at this
    dsimp only at this
    rw [show k + 1 - 1 - (k - i) = i by omega, show k + 1 - 1 - (k - (i + 1)) = i + 1 by omega] at this
    split_ifs at this <;> omega
  have hshift : lam.detShift = lam.w ⟨k, Nat.lt_succ_self k⟩ := by
    simp [DomWeight.detShift]
  set A : ℕ → ℕ := fun i => if i < p then ap i - if i + 1 < p then ap (i + 1) else 0 else 0 with hA
  set B : ℕ → ℕ := fun i => if i < q then am i - if i + 1 < q then am (i + 1) else 0 else 0 with hB
  have eA : (∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) =
      (∏ i ∈ Finset.range k, L (i + 1) ^ A i) * L (k + 1) ^ A k := by
    rw [← Finset.prod_range_succ (fun i => L (i + 1) ^ A i),
      ← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ k + 1 by omega))
        (fun i _ hi => by rw [hA]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hA]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eB : (∏ i ∈ Finset.range q, L (k + 1 - (i + 1)) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
    have : ∏ i ∈ Finset.range (k + 1), L (k + 1 - (i + 1)) ^ B i = ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
      rw [Finset.prod_range_succ, Nat.sub_self, h0, one_pow, mul_one, ← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show k + 1 - (k - 1 - i + 1) = i + 1 by omega]
    rw [← this, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ k + 1 by omega))
        (fun i _ hi => by rw [hB]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hB]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eR : ∏ s : Fin (k + 1), L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ (A i + B (k - 1 - i)) := by
    rw [Fin.prod_univ_castSucc, show lam.natW (Fin.last k) = 0 by
      rw [DomWeight.natW, hshift]; simp [Fin.last], Nat.zero_sub, pow_zero, mul_one,
      ← Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ (A i + B (k - 1 - i)))]
    refine Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨s, hs⟩ := s
    have hs' : s + 1 < k + 1 := by omega
    simp only [Fin.castSucc_mk, Formalism.GradedWeylDivisibility.nuNext, dif_pos hs', DomWeight.natW, hshift]
    congr 1
    have a1 := hanti s (s + 1) (by omega) hs' (by omega)
    have a2 := hanti (s + 1) k hs' (by omega) (by omega)
    have b1 := hl ⟨s, by omega⟩
    have b2 := hl ⟨s + 1, hs'⟩
    dsimp only at b1 b2
    rw [show k + 1 - 1 - s = k - 1 - s + 1 by omega] at b1
    rw [show k + 1 - 1 - (s + 1) = k - 1 - s by omega] at b2
    rw [hA, hB]
    dsimp only
    split_ifs at b1 b2 ⊢ <;> omega
  have eS : lam.detShift = c + (A k : ℤ) - ((if 0 < q then am 0 else 0 : ℕ) : ℤ) := by
    rw [hshift, hl, hA]
    dsimp only
    rw [show k + 1 - 1 - k = 0 by omega]
    split_ifs <;> omega
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [eA, eB, eR, eS, sum_drops q am ham, zpow_sub₀ hd, zpow_add₀ hd, zpow_natCast, zpow_natCast]
  simp only [pow_add, Finset.prod_mul_distrib, inv_pow]
  ring

theorem eval_extremal (lam : D.what₂.Tau → DomWeight n) (y : GLR D n) (τ : D.what₂.Tau) :
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (y v.1).val v.2.1 v.2.2)
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ (extremal ℂ n (lam τ))) =
    ∏ s : Fin n, lead (y τ).val (s + 1) ^ ((lam τ).natW s - Formalism.GradedWeylDivisibility.nuNext (lam τ).natW s) := by
  rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, RingHom.map_det, lead, dif_pos (Nat.succ_le_of_lt s.isLt)]
  congr 2
  ext a b
  simp [Formalism.GradedWeylDivisibility.blockEmb]

theorem harmFn_delta : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  intro D m n w B hw hm
  refine ⟨∏ τ, ∏ i ∈ Finset.range (w.q τ), Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^
    (w.am τ i - if i + 1 < w.q τ then w.am τ (i + 1) else 0), fun x => ?_⟩
  rw [harmFn_apply, coefFn, ten]
  generalize B⁻¹ * x = y
  rw [Weight.delta, Datum.delta, map_prod, map_prod]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, Int.cast_prod, Units.val_pow_eq_pow_val, Int.cast_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := hw.le τ
  have h2 := hm τ
  have hd : lead (y τ).val n ≠ 0 := by
    rw [lead_self]; exact (GeneralLinearGroup.det (y τ)).ne_zero
  rw [eval_extremal, ← lead_self, ← prod_exponents (w.ap τ) (w.am τ) (w.c τ) (w.lam τ) h1 (hw.lam_eq τ) _ (lead_zero _) hd,
    deltaAt, map_mul, map_prod, map_prod,
    Finset.prod_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorPlus w.p y τ (by omega) (by omega) (by omega)],
    Finset.prod_congr (s₁ := Finset.range (w.q τ)) rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorMinus w.p y τ (by omega) (by omega), mul_pow, ← lead_self],
    Finset.prod_mul_distrib]
  ring

end GlobalTheory.ExportSeries.DeltaExtremal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  first | exact @GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | exact GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | (intros; apply GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMemKOneOfSame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniDepthZero

theorem algHom_eq_or_conj {L K : Type} [Field L] [NumberField L] [IsCMField L] [Field K] [Algebra (maximalRealSubfield L) K]
    (φ ψ : L →ₐ[(maximalRealSubfield L)] K) : φ = ψ ∨ φ = ψ.comp (IsCMField.complexConj L).toAlgHom := by
  let e : L ≃ₐ[(maximalRealSubfield L)] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal (maximalRealSubfield L) ψ.fieldRange := Normal.of_algEquiv e
  have hR : φ.fieldRange = ψ.fieldRange := by
    have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
    rw [← h]
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
  have hmem : ∀ z, φ z ∈ ψ.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : L →ₐ[(maximalRealSubfield L)] L := e.symm.toAlgHom.comp (φ.codRestrict ψ.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, ψ (g₀ z) = φ z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hmem z⟩)
    exact this
  let σ : L ≃ₐ[(maximalRealSubfield L)] L := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  have hσ : ∀ z, ψ (σ z) = φ z := hg₀
  have htop := IsCMField.zpowers_complexConj_eq_top L
  have hmemσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj L) := by rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemσ
  have hk2 : IsCMField.complexConj L ^ (k % 2) = σ := by
    have h := zpow_mod_orderOf (IsCMField.complexConj L) k
    rw [IsCMField.orderOf_complexConj L] at h
    rw [← hk]
    exact_mod_cast h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl
  · right
    rw [h1, zpow_one] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem proj_conj {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) (x : AL L) :
    (SplitPlace.proj (⟨v, i⟩ : SplitPlace L)) x = (SplitPlace.proj (⟨v, i₀⟩ : SplitPlace L)) (conjAL L x) := by
  subst hi
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem loc_conj_apply {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) {n : ℕ} (κ : GA L n) (a b : Fin n) :
    (SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ).val a b =
      (SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹).val b a := by
  have hm := κ.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  have h2 : (((κ⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a = conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) := by
    rw [InvMemClass.coe_inv, h1]; rfl
  simp only [SplitPlace.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
  rw [h2, proj_conj v i i₀ hi]

theorem loc_mem_KOne_of_same {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) {n : ℕ} (κ : GA L n)
    (h : SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
  rcases algHom_eq_or_conj i i₀ with rfl | hi
  · exact h
  · have h' : SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
      refine (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).2 fun a b => ?_
      have := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h b a
      simp only [Matrix.sub_apply, Matrix.one_apply] at this ⊢
      rw [← loc_conj_apply v i i₀ hi]
      by_cases hab : a = b
      · subst hab; simpa using this
      · simpa [hab, Ne.symm hab] using this
    have := inv_mem h'
    rwa [map_inv, inv_inv] at this

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem level_trivial {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s₀ : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
    (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)
    (hJ : NG.LevelUni J χ s₀ r ψ₀ ξ) (hψ : NG.IsPsi0 s₀ ψ₀)
    (hξ : ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1)
    (κ : GAf L n) (hκ : TrivOutside {s₀.v} κ)
    (hK : s₀.loc n κ ∈ KOne (s₀.v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1 := by
  set g := s₀.loc n κ with hg
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' g).1 hK
  have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (g.val a b) < 1 := fun a b hab => by
    simpa [Matrix.sub_apply, Matrix.one_apply_ne hab] using hv a b
  have hdiag : ∀ a : Fin n, Valued.v (g.val a a - 1) < 1 := fun a => by
    simpa [Matrix.sub_apply] using hv a a
  have hint : g ∈ Formalism.UG.GLint (Fin n) (s₀.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s₀.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hK
  have huni : NG.UniRT s₀ r g := by
    refine ⟨⟨hint, fun a b ha hb => hoff a b ?_⟩, fun a b ha hb => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · rintro rfl; omega
    · rintro rfl; omega
    · subst hab; exact hdiag a
  have hmem : κ ∈ J := (hJ.mem κ hκ).2 huni
  let D : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s₀.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.of fun a b => g.val a.1 b.1
  have hD : GlobalTheory.StepData.MaxM (D - 1) := by
    have hm := GlobalTheory.StepData.mem_KOne.1 hK
    intro a b
    have h3 := hm a.1 b.1
    by_cases hab : a = b
    · subst hab
      simpa [D, Matrix.sub_apply] using h3
    · have h4 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simpa [D, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne h4] using h3
  obtain ⟨u', hu', hu'v⟩ := GlobalTheory.StepData.exists_mem_KOne hD
  have hdet := GlobalTheory.StepData.det_of_mem_KOne hu'
  have : (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (s₀.v.adicCompletion (maximalRealSubfield L)))
    (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)))
  have hdetv : Valued.v (NG.detDD s₀ r g - 1) < 1 := by
    rw [← he.lt_one_iff_lt_one]
    convert hdet using 3
    rw [Matrix.GeneralLinearGroup.val_det_apply, hu'v]
    rfl
  have hne : NG.detDD s₀ r g ≠ 0 := fun h0 => by
    rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdetv
    exact lt_irrefl _ hdetv
  have hχ := hJ.chr κ hmem hκ (Units.mk0 _ hne) rfl
  have h1 : ψ₀ (NG.supDiag s₀ r g) = 1 := by
    refine hψ.1 _ ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with h
    · exact hoff a b (fun e => by subst e; omega)
    · simp
  have h2 : ξ (Units.mk0 _ hne) = 1 := hξ _ (by simpa using hdetv)
  refine ⟨hmem, Units.ext ?_⟩
  rw [hχ, h1, h2]
  simp

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (s₀ : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ → NG.IsPsi0 s₀ ψ₀ → (∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v = s₀.v → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → fixed (GlobalTheory.LocLanglands.cls σ).rep (KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n a S hS J χ _ s₀ r ψ₀ ξ hJ hψ hξ f hf hfJ hf0 s hs σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hfix : ∀ κ : GAf L n, TrivOutside {s.v} κ →
      s.loc n κ ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f := by
    intro κ hκ hK
    obtain ⟨v, i⟩ := s
    obtain ⟨v₀, i₀⟩ := s₀
    obtain rfl : v = v₀ := hs
    have hK₀ := loc_mem_KOne_of_same _ i i₀ κ hK
    obtain ⟨hm, h1⟩ := level_trivial J χ _ r ψ₀ ξ hJ hψ hξ κ hκ hK₀
    have h2 := hfJ.2 ⟨κ, hm⟩
    rw [h1] at h2
    simpa using h2
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1
    (fun g hg => by
      rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
      exact GlobalTheory.StepData.KOne_le_KO hg)
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hf hf0 (fun κ hκ h => by rw [hfix κ hκ h]; simp)
  refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep σ).some.symm ?_
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3

end GlobalTheory.UniDepthZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivCover.OpenKerChar


set_option maxHeartbeats 400000 in
theorem map_eq_one_of_finPart_eq_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A),
    IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  intro D A _ χ hχ x hx
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hfam : GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace D.host.E => w.embedding) := by
    unfold GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  choose θ hθ using fun w : InfinitePlace D.host.E =>
    (GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm w.embedding).exists
  obtain ⟨e2, -, hc2, hc2', -⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig (InfinitePlace D.host.E) _ θ hcm hfam hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h2 : (e1 (x : AE D)).2 = 1 := (he1 _).2.trans hx
  set c : InfinitePlace D.host.E → ℂ := e2 (e1 (x : AE D)).1 with hcdef
  have hcu : IsUnit c := by
    have hu : IsUnit (e1 (x : AE D)) := x.isUnit.map e1
    exact (Prod.isUnit_iff.1 hu).1.map e2
  have hc0 : ∀ w, c w ≠ 0 := fun w => (Pi.isUnit_iff.1 hcu w).ne_zero
  let p : ℝ → (InfinitePlace D.host.E → ℂ) := fun t w => Complex.exp (t * Complex.log (c w))
  let γ : ℝ → AE D := fun t => e1.symm (e2.symm (p t), 1)
  have hpc : Continuous p := continuous_pi fun w =>
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hγc : Continuous γ := hc1'.comp ((hc2'.comp hpc).prodMk continuous_const)
  have hpmul : ∀ s t, p s * p t = p (s + t) := fun s t => by
    funext w
    simp only [p, Pi.mul_apply, ← Complex.exp_add, Complex.ofReal_add, add_mul]
  have hγmul : ∀ s t, γ s * γ t = γ (s + t) := fun s t => by
    simp only [γ, ← map_mul, Prod.mk_mul_mk, mul_one, hpmul]
  have hp0 : p 0 = 1 := by funext w; simp [p]
  have hγ0 : γ 0 = 1 := by simp only [γ, hp0, map_one, Prod.mk_one_one]
  have hp1 : p 1 = c := by funext w; simp [p, Complex.exp_log (hc0 w)]
  have hγ1 : γ 1 = x := by
    simp only [γ, hp1, hcdef, RingEquiv.symm_apply_apply]
    rw [← h2, Prod.mk.eta, RingEquiv.symm_apply_apply]
  have hr : ∀ t, γ t * γ (-t) = 1 := fun t =>
    (hγmul t (-t)).trans ((congrArg γ (add_neg_cancel t)).trans hγ0)
  have hl : ∀ t, γ (-t) * γ t = 1 := fun t =>
    (hγmul (-t) t).trans ((congrArg γ (neg_add_cancel t)).trans hγ0)
  let f : ℝ → (AE D)ˣ := fun t => Units.mk (γ t) (γ (-t)) (hr t) (hl t)
  have hf : Continuous f := Units.continuous_iff.2 ⟨hγc, hγc.comp continuous_neg⟩
  have hcl : IsClosed (χ.ker : Set (AE D)ˣ) := Subgroup.isClosed_of_isOpen _ hχ
  have hS : IsClopen (f ⁻¹' (χ.ker : Set (AE D)ˣ)) := ⟨hcl.preimage hf, hχ.preimage hf⟩
  have h0 : (0 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := by
    have : f 0 = 1 := Units.ext hγ0
    simp [this]
  rcases isClopen_iff.1 hS with h | h
  · rw [h] at h0; exact absurd h0 (Set.notMem_empty _)
  · have h1 : (1 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := h ▸ Set.mem_univ _
    have hf1 : f 1 = x := Units.ext hγ1
    rw [Set.mem_preimage, hf1] at h1
    exact h1

end GlobalTheory.UnivCover.OpenKerChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOneStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  first | exact @GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | exact GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | (intros; apply GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one <;> assumption)
end
end

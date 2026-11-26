module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormLt
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem exists_extend_residue {O A F : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Algebra.IsIntegral O A] (hinj : Function.Injective (algebraMap O A)) [Field F] [IsAlgClosed F]
    (κ : IsLocalRing.ResidueField O →+* F) :
    ∃ g : A →+* F, g.comp (algebraMap O A) = κ.comp (IsLocalRing.residue O) := by
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (IsLocalRing.maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (A ⧸ Q) := Ideal.Quotient.field Q
  let j : IsLocalRing.ResidueField O →+* A ⧸ Q := Ideal.quotientMap Q (algebraMap O A) hQm.ge
  have hj : j.comp (IsLocalRing.residue O) = (Ideal.Quotient.mk Q).comp (algebraMap O A) := by
    ext x; rfl
  letI : Algebra (IsLocalRing.ResidueField O) (A ⧸ Q) := j.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) F := κ.toAlgebra
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
    refine ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (j.comp (IsLocalRing.residue O)) _ _ = 0
    rw [hj, ← hom_eval₂, hpa, map_zero]⟩
  let L : (A ⧸ Q) →ₐ[IsLocalRing.ResidueField O] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  rw [RingHom.comp_assoc, ← hj, ← RingHom.comp_assoc]
  congr 1
  ext x
  exact L.commutes x

theorem exists_redVia : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
      InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  intro D i k _
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hφ : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  letI : Algebra (D.nd.O i) ℂ := (iotaO D.nd D.naut i).toAlgebra
  let A := integralClosure (D.nd.O i) ℂ
  have hA : Function.Injective (algebraMap (D.nd.O i) A) := fun x y h => hφ (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_extend_residue hA (D.naut.kFbar i)
  have hmem : ∀ x, D.ntypes.teichC k x ∈ A := by
    intro x
    by_cases hx : x = 0
    · rw [hx, GlobalTheory.TameLabels.teich_zero _ (D.ntypes.teichC_inj k)]; exact A.zero_mem
    · obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1
        ((D.ntypes.teichC k).isOfFinOrder (GlobalTheory.TameLabels.isOfFinOrder_of_ne_zero hx))
      exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  let t : Fb (D.host.g k) (D.host.g_prime k) →* A := (D.ntypes.teichC k).codRestrict A.toSubmonoid hmem
  have ht : ∀ x, (t x : ℂ) = D.ntypes.teichC k x := fun _ => rfl
  refine ⟨g.toMonoidHom.comp t, fun x y hx hy hcx hcy h => ?_, fun p s hp => ?_⟩
  · refine D.ntypes.teichC_inj k x y hx hy ?_
    rw [← ht, ← ht]
    congr 1
    refine GlobalTheory.TameRed.eq_of_map_eq g (M := orderOf x * orderOf y) ?_ ?_ ?_ h
    · rw [Ne, CharP.cast_eq_zero_iff _ (D.nd.l i)]
      exact (Nat.Prime.coprime_iff_not_dvd (D.nd.lPrime i).out).1 (Nat.Coprime.mul_left hcx hcy).symm
    · rw [← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
    · rw [← map_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
  · have h1 : p.map (algebraMap (D.nd.O i) A) = (s.map fun x => X - C (t x)).prod := by
      apply Polynomial.map_injective A.val.toRingHom Subtype.val_injective
      rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
      refine hp.trans (congrArg _ (Multiset.map_congr rfl fun x _ => ?_))
      simp [ht]
    rw [← hg, ← Polynomial.map_map, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
    simp

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatioStatement
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k → ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  first | exact @GlobalTheory.TypeLeaf.exists_redVia | exact GlobalTheory.TypeLeaf.exists_redVia | (intros; apply GlobalTheory.TypeLeaf.exists_redVia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrime
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem actWCbHom_teichmuller_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (g : GQ l) (c : Cb l) :
    AI.actWCbHom g (WittVector.teichmuller l c) =
      WittVector.teichmuller l (autCb l (AI.actT g) c) :=
  WittVector.map_teichmuller l (autCb l (AI.actT g)).toRingHom c

theorem exists_fix_lift_of_fix_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL)
    (h : ∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) :
    ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  obtain ⟨y, hy⟩ : ∃ y : RW LL, ∀ i, crd (basisO LL) i y =
      WittVector.teichmuller l ((crd (basisO LL) i x).coeff 0) :=
    ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ((crd (basisO LL) j x).coeff 0),
      fun i => crd_sum (basisO LL) _ i⟩
  refine ⟨y, mem_fixSub.2 fun g hg => ext_crd (basisO LL) fun i => ?_,
    (dvd_iff_crd LL _).2 fun i => ?_⟩
  · have h1 := (dvd_iff_crd LL _).1 (h g hg) i
    rw [LinearMap.map_sub, sub_coeff_zero, crd_gRW, coeff_actWCbHom] at h1
    rw [crd_gRW, hy, actWCbHom_teichmuller_eq, sub_eq_zero.1 h1]
  · rw [LinearMap.map_sub, sub_coeff_zero, hy, WittVector.teichmuller_coeff_zero, sub_self]

end GlobalTheory.Decompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrimeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) (x : RW LL), (∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) → ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | exact GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | (intros; apply GlobalTheory.Decompl.exists_fix_lift_of_fix_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Generic

variable {A R : Type} [CommRing A] [CommRing R] {ι : A →+* R} {p : ℕ} {t : R}

theorem Near.map_of_fixed (g : R →+* R) (hg : ∀ a, ∃ b, ι b = g (ι a)) (ht : g t = t) {m : ℕ}
    {x : R} (hx : Near ι p t m x) : Near ι p t m (g x) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hg a
  exact ⟨b, g r, by rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, ht, hb]⟩

theorem fixed_complete_generic {G : Type} (H : Set G) (act : G → (R →+* R)) (S : Subring R)
    (hS : ∀ x, x ∈ S ↔ ∀ g ∈ H, act g x = x) {τ : A} (hτ : ι τ = t)
    (hg : ∀ g a, ∃ b, ι b = act g (ι a))
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hcomp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, Near ι p t (i + k) (f i)) →
      ∃ x, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hlift : ∀ x : R, (∀ g ∈ H, ∃ r, act g x - x = (p : R) * r) →
      ∃ y ∈ S, ∃ r, y - x = (p : R) * r)
    (ht : t ∈ S) (k : ℕ) (f : ℕ → R) (hf : ∀ i, f i ∈ S) (hn : ∀ i, Near ι p t (i + k) (f i)) :
    ∃ x ∈ S, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  obtain ⟨x, hx⟩ := hcomp k f hn
  obtain ⟨y, hy, r, hr⟩ := hlift x fun g hgH => hsep _ fun m => by
    have h1 : act g (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, f i :=
      (hS _).1 (S.sum_mem fun i _ => hf i) g hgH
    have h2 := (Near.map_of_fixed (act g) (hg g) ((hS _).1 ht g hgH) (hx m)).sub (hx m)
    rw [map_sub, h1, sub_sub_sub_cancel_right] at h2
    exact h2.mono hτ (Nat.le_add_right m k)
  refine ⟨y, hy, fun m => ?_⟩
  have h3 := (Near.of_mul (ι := ι) (p := p) (t := t) (m + k) r).add (hx m)
  rw [← hr, sub_add_sub_cancel] at h3
  exact h3

end Generic

theorem fixSub_nearPi_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  intro l _ P AI LL s H
  exact fixed_complete_generic H (fun g => (AI.gRW LL g : RW LL →+* RW LL)) (fixSub AI LL H)
    (fun _ => mem_fixSub) (τ := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
    (fun g a => ⟨GlobalTheory.Cyc.Decomp.gRA AI LL g a, GlobalTheory.Cyc.Decomp.inclR_gRA AI LL g a⟩)
    (GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s).1 (GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s).2 (GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime l P AI LL H)

end GlobalTheory.Decompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEllStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.fixSub_nearPi_complete | exact GlobalTheory.Decompl.fixSub_nearPi_complete | (intros; apply GlobalTheory.Decompl.fixSub_nearPi_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.WachHyp

theorem jump_mem (S : LocalSituation.Sit) (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (h : IsJumpV S.PD T.ρ τ a) : a ∈ LocalSituation.Jset S T := by
  intro e
  apply h
  unfold FildR DdRE
  rw [inf_right_comm, e, inf_right_comm]

theorem jumpsLet_const (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    DeltaInvariantLattices.JumpsLet S.W Y (fun _ => M0) (fun _ => h0) := by
  intro τ i _ a ha
  exact Set.mem_Icc.2 (hj a (jump_mem S Y τ a ha))

theorem nBasis (S : LocalSituation.Sit) (E : S.Comparison₂) (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O)
    (hY : IsCrys S.PD Y.ρ) : LocalSituation.NBasis S E Y (S.W.N Y) := by
  obtain ⟨⟨⟨r, b, hbN, huniq, hRW⟩, -⟩, -⟩ := he Y hY
  let v : Fin r → ↥(S.W.N Y) := fun j => ⟨b j, hbN j⟩
  have hli : LinearIndependent (LetA S.O S.n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ((∑ j, g j • v j : ↥(S.W.N Y)) : S.W.DD Y) = 0 := by rw [hg]; rfl
    have h0' : (0 : S.W.DD Y) = ∑ j, g j • b j := by
      rw [← h0]; simp [v]
    obtain ⟨a, -, ha⟩ := huniq 0 (S.W.N Y).zero_mem
    have e1 := ha g h0'
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  have hsp : ⊤ ≤ Submodule.span (LetA S.O S.n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(S.W.N Y)) = ∑ j, a j • v j := by
      apply Subtype.ext
      simp [v, ha]
    rw [this]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Fin r, inferInstance, Module.Basis.mk hli hsp, ?_, ?_⟩
  · simp only [Module.Basis.mk_apply, v]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨a, -, ha⟩ := hRW 0
    have e1 := ha c hc.symm
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  · simp only [Module.Basis.mk_apply, v]
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, hc, -⟩ := hRW y
    rw [hc]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem wClauses (S : LocalSituation.Sit) (E : S.Comparison₂) (h1 : DeltaInvariantLattices.WachLatticeFree S.W) (h5 : DeltaInvariantLattices.P5W S.W)
    (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (hY : IsCrys S.PD Y.ρ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    LocalSituation.WClauses S E Y M0 h0 (S.W.N Y) := by
  have hf := h1 Y hY
  have hp := h5 Y (fun _ => M0) (fun _ => h0) hY (jumpsLet_const S Y M0 h0 hj)
  have hNl : ∀ i, S.W.Nl Y i ≤ S.W.N Y := fun i => by
    rw [hf.1]; exact le_iSup (fun j => S.W.Nl Y j) i
  refine ⟨nBasis S E he Y hY, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hf.1] at hx
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun x => S.W.Q ^ M0 • S.W.φD Y x ∈ S.W.N Y) hx ?_ ?_ ?_
    · intro j y hy
      exact hp.1 (j + 1) y (by simpa using hy)
    · simp
    · intro y z hy hz
      simp only [map_add (f := _), smul_add]
      exact add_mem hy hz
  · intro y hy
    rw [hf.1] at hy
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun y => S.W.Q ^ h0 • y ∈ LocalSituation.phiSpan S Y (S.W.N Y)) hy ?_ ?_ ?_
    · intro j y hy
      exact Submodule.span_mono (Set.image_mono (hNl (j - 1))) (hp.2.1 j y hy)
    · simp
    · intro y z hy hz
      simp only [smul_add]
      exact add_mem hy hz
  · intro g _ x hx
    exact S.W.N_Γ Y _ x hx
  · intro g _ x hx
    obtain ⟨y, hy, e⟩ := S.W.N_π Y (S.W.resΓ g) x hx
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hy
  · intro f x hx
    exact S.W.map_N f hY hY x hx

theorem hypW_crystalline : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  intro D HW F Cm hU hE hC l _ K s LL h Y M0 h0 hY hj
  have hT := hU.1 l K s LL h
  exact LocalSituation.HypW_of_rec (hC l K s LL h Y hY) hj
    (wClauses _ _ hT.1 hT.2.2.2.2.1 (hE.1 l K s LL h) Y M0 h0 hY hj)

end GlobalTheory.WachHyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLatticesStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachHypothesis_crystallineLattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  first | exact @GlobalTheory.WachHyp.hypW_crystalline | exact GlobalTheory.WachHyp.hypW_crystalline | (intros; apply GlobalTheory.WachHyp.hypW_crystalline <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATop
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakClosed

theorem compactSpace_oTop {l : ℕ} [Fact l.Prime] {LL : FinExt l} {e : ℕ}
    (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    @CompactSpace ↥(OL LL) (oTop bO) := by
  letI := oTop bO
  have hi : Topology.IsInducing (bO.equivFun : ↥(OL LL) → (Fin e → ℤ_[l])) := ⟨rfl⟩
  refine ⟨?_⟩
  rw [hi.isCompact_iff, Set.image_univ_of_surjective bO.equivFun.surjective]
  exact isCompact_univ

theorem compactSpace_aTop : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)), letI := aTop (K := K) bO; CompactSpace (AA K LL) := by
  intro l _ K LL e bO
  letI := oTop bO
  haveI := compactSpace_oTop bO
  haveI : CompactSpace (PowerSeries ↥(OL LL)) := by
    unfold PowerSeries MvPowerSeries
    exact Pi.compactSpace
  exact Pi.compactSpace

end GlobalTheory.WeakClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamified
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_herbrandPhi_natCast_of_totallyRamified (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] :
    lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a =
      ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  intro h0 a
  induction a with
  | zero => simp
  | succ n ih =>
    have hstep := herbrandPhi_of_mem_Icc (K := F) (L := L) n (u := ((n : ℝ) + 1))
      ⟨by linarith, le_refl _⟩
    have hidx : (lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup F L 0) *
        Nat.card ↥(wild F L n) = Nat.card (L ≃ₐ[F] L) := by
      rw [h0, Subgroup.relIndex_top_right, wild, Subgroup.index_mul_card]
    have hpos : (0 : ℝ) < ((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℝ) := relIndex_pos_of_finite _ _
    have hidxR : (((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℕ) : ℝ) * (Nat.card ↥(wild F L n) : ℝ) =
        (Nat.card (L ≃ₐ[F] L) : ℝ) := by exact_mod_cast hidx
    push_cast [Finset.sum_range_succ] at ih ⊢
    rw [hstep, ← ih, ← hidxR]
    field_simp
    ring

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L], lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a = ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | exact GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified | (intros; apply GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryIffIsCrys
noncomputable section

namespace GlobalTheory.CrysExtCrit

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem exists_form {L V₀ V₁ : Type} [Field L] [AddCommGroup V₀] [Module L V₀] [AddCommGroup V₁] [Module L V₁]
    [FiniteDimensional L V₁] (ι : V₀ →ₗ[L] V₁) (hι : Function.Injective ι)
    (hd : finrank L V₁ = finrank L V₀ + 1) (x : V₁) (hx : x ∉ LinearMap.range ι) :
    ∃ p : V₁ →ₗ[L] L, p x = 1 ∧ LinearMap.ker p = LinearMap.range ι := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hle : LinearMap.range ι ≤ LinearMap.ker ((f x)⁻¹ • f) := by
    intro y hy
    have : f y = 0 := by
      have : f y ∈ (LinearMap.range ι).map f := ⟨y, hy, rfl⟩
      rwa [hf0, Submodule.mem_bot] at this
    simp [this]
  have hpx : ((f x)⁻¹ • f) x = 1 := by simp [hf]
  refine ⟨(f x)⁻¹ • f, hpx, (Submodule.eq_of_le_of_finrank_le hle ?_).symm⟩
  have hne : LinearMap.ker ((f x)⁻¹ • f) ≠ ⊤ := fun h => by
    have : x ∈ LinearMap.ker ((f x)⁻¹ • f) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hpx] at this
    exact one_ne_zero this
  have := Submodule.finrank_lt hne
  rw [LinearMap.finrank_range_of_inj hι]
  omega

theorem coboundary_iff_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (ι : V₀ →ₗ[↥LL.1] V₁), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → Function.Injective ι → finrank ↥LL.1 V₁ = finrank ↥LL.1 V₀ + 1 → IsCrys (P.PD K) ρ₀ → ∀ x : V₁, x ∉ LinearMap.range ι → ∀ c : ↥(GK K) → V₀, (∀ g, ι (c g) = ρ₁ g x - x) → ((∃ y : V₀ ⊗[ℚ_[l]] P.R.B, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ₀ g y - y) ↔ IsCrys (P.PD K) ρ₁) := by
  intro l _ P AI _ K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ ι hιρ hι hd hV x hx c hc
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨p, hpx, hk⟩ := exists_form ι hι hd x hx
  have hex : Function.Exact ι p := LinearMap.exact_iff.2 hk
  have hs : Function.Surjective p := fun a => ⟨a • x, by simp [hpx]⟩
  have hinv : ∀ g y, p (ρ₁ g y) = p y := by
    intro g y
    obtain ⟨v, hv⟩ := (hex (y - p y • x)).1 (by simp [hpx])
    have h1 : ρ₁ g y = ι (ρ₀ g v) + p y • (ι (c g) + x) := by
      rw [hιρ, hv, hc, map_sub, map_smul, sub_add_cancel, sub_add_cancel]
    rw [h1]
    simp [hex.apply_apply_eq_zero, hpx]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt ρ₀ ρ₁ ι p := ⟨hι, hex, hs, hιρ, hinv⟩
  have hc' : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf ρ₁ ι p c := ⟨x, hpx, fun g => by rw [hc, add_sub_cancel]⟩
  rw [GlobalTheory.CrysExt.isCrys_iff_surjective (P.PD K) hV h, ← GlobalTheory.CrysExt.lift_iff_surjective (P.PD K) h,
    ← GlobalTheory.CrysExt.coboundary_iff_lift (P.PD K) h hc']

end GlobalTheory.CrysExtCrit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmul
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_one_tmul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro l _ K LL T d b
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  letI := zlMod T
  haveI := zlTower T
  letI := twTop T b
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hb : ∀ i, Continuous fun t : ↥T.L.T => b.repr t i := by
    intro i
    obtain ⟨φ, hφ⟩ := GlobalTheory.Cyc.exists_form_lat hc T b i
    have h1 : Continuous φ := GlobalTheory.Cyc.continuous_form_of_moduleTopology (L := ↥LL.1) φ
    exact hemb.continuous_iff.2 ((h1.comp continuous_subtype_val).congr hφ)
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  have h1 : ∀ (t : ↥T.L.T) i, GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b
      ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) i = algebraMap ℤ_[l] (WCb l) (b.repr t i) := by
    intro t i
    rw [Algebra.TensorProduct.one_def, GlobalTheory.WeakTop.coords_tmul, one_smul,
      Algebra.algebraMap_eq_smul_one]
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, h1]
  exact hW.comp (hb i)

end GlobalTheory.WeakClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmulStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_tmul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  first | exact @GlobalTheory.WeakClosed.continuous_one_tmul | exact GlobalTheory.WeakClosed.continuous_one_tmul | (intros; apply GlobalTheory.WeakClosed.continuous_one_tmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRange
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.NL.WkRange

theorem jD_smul_letter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) (x : W.DD T) :
    E.tie.jD T (a • x) = inclR LL (E.tie.io a) • E.tie.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.tie.jD_smul, E.tie.ioE_ext]

theorem jD_aN_eq_range : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  intro l _ P AI K s LL h W E T
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T ((letπ : AA K LL) • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • ((letπ : AA K LL) • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum]
      exact Finset.sum_congr rfl fun i _ => jD_smul_letter E T _ _

end GlobalTheory.NL.WkRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRangeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_aN_eq_range_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  first | exact @GlobalTheory.NL.WkRange.jD_aN_eq_range | exact GlobalTheory.NL.WkRange.jD_aN_eq_range | (intros; apply GlobalTheory.NL.WkRange.jD_aN_eq_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosure
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatInvariants

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem root_pow (j : ℕ) : AI.εroot j ^ l ^ j = AI.ε := by
  induction j with
  | zero => simp [LocAinf.εroot]
  | succ j ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem root_sub_dvd (j : ℕ) : AI.εroot j - 1 ∣ AI.ε - 1 := by
  rw [← root_pow AI j]
  exact sub_one_dvd_pow_sub_one _ _

theorem exists_pow_mul_integral (s : ℕ) (y : Cb l) : ∃ k, ∀ k' ≥ k, ∃ z : OCb l,
    algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ k') * y = algebraMap (OCb l) (Cb l) z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, hk⟩ : ∃ k, b ∣ (AI.εroot s - 1) ^ k := by
    by_contra h
    exact hb0 ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 b fun m =>
      (ValuationRing.dvd_total _ _).resolve_right fun h' => h ⟨m, h'⟩)
  refine ⟨k, fun k' hk' => ?_⟩
  obtain ⟨d, hd⟩ := hk.trans (pow_dvd_pow _ hk')
  have : algebraMap (OCb l) (Cb l) b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm))
  refine ⟨d * a, ?_⟩
  rw [hd, map_mul, map_mul]
  field_simp

theorem flat_invariant_approx : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  intro l _ P AI K s w hw m
  obtain ⟨k, hk⟩ := exists_pow_mul_integral AI s w
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨z, hz⟩ := hk N hN
  have hfix : ∀ g ∈ Hinf K, AI.actT g z = z := fun g hg => by
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← autCb_alg, ← hz, map_mul, hw g hg, autCb_alg, map_pow (AI.actT g), map_sub (AI.actT g), map_one (AI.actT g),
      (GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).1 g hg s]
  obtain ⟨u, hu, hd⟩ := GlobalTheory.TiltInvariants.invariant_approx l P AI K z hfix (N + m)
  obtain ⟨v, hv⟩ := (pow_dvd_pow_of_dvd (root_sub_dvd AI s) (N + m)).trans hd
  exact ⟨u, hu, v, by rw [hz, ← hv, add_sub_cancel]⟩

end GlobalTheory.FlatInvariants
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosureStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_invariant_approx_by_epsilonRoots_closure : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  first | exact @GlobalTheory.FlatInvariants.flat_invariant_approx | exact GlobalTheory.FlatInvariants.flat_invariant_approx | (intros; apply GlobalTheory.FlatInvariants.flat_invariant_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
noncomputable section

open GlobalTheory.WachUse GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

namespace GlobalTheory.WachUse.HeightsProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letφ_letE (i : ZMod n) : letφ W.φ₀ (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have hj' : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, hj']

theorem φD_letE (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE (letE (i - 1))) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul, letφ_letE] at this

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

theorem of_heightBounds (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hb : HeightBounds W T M h) (i : ZMod n) :
    (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
      ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T := by
  refine ⟨fun x hx => Nl_le W T i ((hb i).1 _ ?_), fun y hy => ?_⟩
  · rw [← φD_letE]
    exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Nl_le W T (i - 1))) ((hb i).2 _ ⟨y, hy, rfl⟩)

theorem jumpsOverLetters_of_crysWith (T : LocLat G Qp LL O) [FiniteDimensional LL ↥(DdR PD T.ρ)]
    (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ) (hU : CrysWith PD W.emb T.ρ U)
    (hb : ∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) : JumpsOverLetters W T M h := by
  intro i τ hτ a ha
  have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite PD T.ρ τ a).2.2.1 ha
  rw [hU.2 i τ hτ a] at h1
  exact hb i a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))

end Generic

theorem heights_of_finite {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hJ : HeightsFromJumps l P AI H E C)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (hfin : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) T.ρ)) :
    Heights (H.W K s LL h) := by
  intro T U M hh hU hb
  haveI := hfin T
  exact of_heightBounds _ T M hh
    (hJ K s LL h T hU.1 M hh (jumpsOverLetters_of_crysWith _ T U M hh hU hb)).1

theorem heights_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H E C → ∀ (K LL : FinExt l) (h : CaseA K LL), Heights (H.W K 1 LL h.2.2) := by
  rintro l _ P AI H E C ⟨Ti⟩ hJ K LL h
  exact heights_of_finite hJ K 1 LL h.2.2 fun T => (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Ti K LL T.V T.ρ).1

end GlobalTheory.WachUse.HeightsProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdeleLogNormCompare

open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.Mem.Chr.CharModel

variable (E : Type) [Field E] [NumberField E]

theorem ord_eq_ord_vw (d : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    GroundTheory.Global.IdeleGroup.ord v d = GlobalTheory.Idele.ord_vw (finPart E d) v := rfl

theorem logInf_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logInf E (infPart E d) = Real.log (infiniteModule d) := by
  rw [infiniteModule, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero d w))

theorem logFin_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logFin E (finPart E d) = -Real.log (finiteModule d) := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (finPart E d))
  let S := hfin.toFinset
  have hS : ∀ v, v ∉ S → GlobalTheory.Idele.ord_vw (finPart E d) v = 0 := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hI : GlobalTheory.Idele.idealOf (finPart E d) =
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v := by
    unfold GlobalTheory.Idele.idealOf
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    exact hv (by show (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v = 1
                 rw [hS v h, zpow_zero])
  have hM : finiteModule d = ∏ v ∈ S, ‖(d : AdeleRing (𝓞 E) E).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    refine hv ?_
    change ‖(d : AdeleRing (𝓞 E) E).2 v‖ = 1
    rw [norm_finite_eq_rpow, ord_eq_ord_vw, hS v h, Int.cast_zero, neg_zero, Real.rpow_zero]
  have hN : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    fun v => (absNorm_asIdeal_pos v).ne'
  rw [logFin, hI, hM, map_prod, Rat.cast_prod, Real.log_prod, Real.log_prod, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow,
      norm_finite_eq_rpow, Real.log_rpow (absNorm_asIdeal_pos v), ord_eq_ord_vw]
    ring
  · intro v _
    exact norm_ne_zero_iff.2 (finite_ne_zero d v)
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (hN v)

theorem logNorm_eq_log_ideleModule (d : (AdeleRing (𝓞 E) E)ˣ) :
    logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  rw [logNorm, logInf_eq, logFin_eq, ideleModule_apply,
    Real.log_mul (infiniteModule_pos d).ne' (finiteModule_pos d).ne']
  ring

end GlobalTheory.IdeleLogNormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModuleStatement
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLe
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  intro l _ ι s r x hr hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : sh (0 : Fl l) = 0 := by
      have h : (0 : Fl l).untilt = 0 := Perfection.teichmuller_zero
      simp only [sh, h]; rfl
    simp only [Finset.sum_empty, h0, sub_zero, norm_zero]
    exact ⟨mul_nonneg (norm_nonneg _) hr, hr⟩
  | insert a t ha ih =>
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hxa : ‖sh (x a)‖ ≤ r := hs a (Finset.mem_insert_self a t)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (x a) (∑ i ∈ t, x i) hxa ih'.2
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, h2⟩
    have : sh (x a + ∑ i ∈ t, x i) - (sh (x a) + ∑ i ∈ t, sh (x i)) =
        (sh (x a + ∑ i ∈ t, x i) - sh (x a) - sh (∑ i ∈ t, x i)) + (sh (∑ i ∈ t, x i) - ∑ i ∈ t, sh (x i)) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih'.1)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sh_sum_sub_sum_sh_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  first | exact @GlobalTheory.untilt_sum_sub_le | exact GlobalTheory.untilt_sum_sub_le | (intros; apply GlobalTheory.untilt_sum_sub_le <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSubquotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ParAsm

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r] at *
  omega

end GlobalTheory.ParAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
noncomputable section

namespace GlobalTheory.LiftChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem charAt (D : D7) (cf : CharFrame D) (C : CharSide D cf) (j : Fin D.R.m) :
    ∃ μ : D.naut.CG 1, (C.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧
      (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧
      ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧
        D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have hm := cf.isMu0 j
  refine ⟨C.e1.symm ⟨cf.mu0 j, hm.unitary⟩, by simp, ?_, ?_, ?_⟩
  · rw [C.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ hm.triv
  · intro w hw
    refine ⟨(C.unr_iff _ w).2 ?_, (C.unr_iff _ w).2 ?_⟩
    · rw [Equiv.apply_symm_apply]
      refine hm.unr w fun k hk => hw ?_
      exact (Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
    · rw [C.etaTinv]
      intro x hx
      have := cf.isEta.unr w x hx
      show ((cf.eta.loc w) x)⁻¹ = 1
      rw [this, inv_one]
  · have hinf : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => -(1/2 : ℚ)) := by
      rw [C.etaTinv]
      refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
      have h := cf.isEta.inf k
      show (((cf.eta.inf k)⁻¹ : ℂˣ) : ℂ) = _
      rw [Units.val_inv_eq_inv_val, h]
      simp only [zpow_one, zpow_neg_one, Finset.prod_inv_distrib]
    intro τ
    obtain ⟨h1, h2⟩ := C.infG _ _ hinf (D.eTau τ)
    refine ⟨?_, ?_⟩
    · show D.naut.infG _ (embPsi D.host (D.eTau τ)) = _
      rw [h1]
      congr 1
      push_cast
      ring
    · show D.naut.infG _ ((starRingEnd ℂ).comp (embPsi D.host (D.eTau τ))) = _
      rw [h2]
      congr 1
      push_cast
      ring

end GlobalTheory.LiftChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LiftInfRef

open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def w0 (n : ℕ) : GL (Fin n) ℂ :=
  ⟨(Fin.revPerm.toPEquiv).toMatrix, (Fin.revPerm.toPEquiv).toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem longestWeylElementGL_mul_self (n : ℕ) : w0 n * w0 n = 1 := by
  ext i j
  simp only [w0, Units.val_mul, Units.val_one]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem longestWeylElementGL_conj_apply_rev (X : GL (Fin n) ℂ) (i j : Fin n) :
    (w0 n * X * w0 n).val i j = X.val (Fin.rev i) (Fin.rev j) := by
  simp only [w0, Units.val_mul]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

def tinv (B : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨(B⁻¹ : GL (Fin n) ℂ).valᵀ, B.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

omit [NumberField L] [IsCMField L] in
theorem conj_conj (τ : L →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem conj_ne (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  intro h
  have h1 : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 h
  have h2 := IsTotallyComplex.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h2
  exact h2 h1

theorem evPt_eq_tinv (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    evPt τ B = evPt (ComplexEmbedding.conjugate τ) (tinv B) := by
  have hne := conj_ne τ
  funext p
  rcases p with ⟨σ, i, j⟩
  by_cases h1 : σ = τ
  · subst h1
    simp [NG.evPt, tinv, Ne.symm hne]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [NG.evPt, tinv, hne]
    · have h3 : σ ≠ ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) := by rwa [conj_conj]
      simp [NG.evPt, h1, h2, h3]

theorem inv_upper {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) : (B⁻¹).val.BlockTriangular id := by
  haveI : Invertible B.val := B.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB

theorem inv_diag {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) (k : Fin n) :
    (B⁻¹).val k k = (B.val k k)⁻¹ := by
  have hI := inv_upper hB
  have e : ((B⁻¹).val * B.val) k k = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hI h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem hwAt_of_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam' : Fin n → ℤ}
    (h : a.HWAt (ComplexEmbedding.conjugate τ) lam') : a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  obtain ⟨ι, hι1, hι2, b, P, hP, v, hv0, hv⟩ := h
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP (ComplexEmbedding.conjugate τ)
  refine ⟨ι, hι1, hι2, b, P, hP, evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v, ?_, fun B hB => ?_⟩
  · intro h0
    apply hv0
    have := congrArg (fun x => evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ x) h0
    simp only [mulVec_mulVec, mulVec_zero] at this
    rwa [← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec] at this
  · set C : GL (Fin n) ℂ := w0 n * tinv B * w0 n with hCdef
    have hBC : tinv B = w0 n * C * w0 n := by
      rw [hCdef, ← mul_assoc, ← mul_assoc, longestWeylElementGL_mul_self, one_mul, mul_assoc, longestWeylElementGL_mul_self, mul_one]
    have hCa : ∀ i j, C.val i j = (B⁻¹).val (Fin.rev j) (Fin.rev i) := by
      intro i j; rw [hCdef, longestWeylElementGL_conj_apply_rev]; rfl
    have hC : C.val.BlockTriangular id := by
      intro i j hij
      rw [hCa]
      exact inv_upper hB (show Fin.rev i < Fin.rev j from Fin.rev_lt_rev.2 hij)
    have hCd : ∀ i, C.val i i = (B.val (Fin.rev i) (Fin.rev i))⁻¹ := fun i => by rw [hCa, inv_diag hB]
    have e1 : (Matrix.of fun i j => MvPolynomial.eval (evPt τ B) (P i j)) =
        evM P (evPt (ComplexEmbedding.conjugate τ) (tinv B)) := by
      rw [evPt_eq_tinv τ B]; rfl
    have hww : evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ
        (evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec]
    have hvC : evM P (NG.evPt (ComplexEmbedding.conjugate τ) C) *ᵥ v = (∏ i, (C.val i i) ^ (lam' i)) • v := hv C hC
    rw [e1, hBC, hR.mul, hR.mul, ← mulVec_mulVec, ← mulVec_mulVec, hww, hvC, mulVec_smul]
    congr 1
    rw [Finset.prod_congr rfl fun i _ => by rw [hCd i, _root_.inv_zpow']]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp [Fin.rev_rev])

end Conj

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem infOf_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam lam' : Fin n → ℤ} (h : a.HWAt τ lam)
    (h' : a.HWAt (ComplexEmbedding.conjugate τ) lam') : infOf lam' = (infOf lam).map Neg.neg := by
  have e := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone L n a τ).1.unique h (hwAt_of_conj h')
  have hl : lam' = fun i => -lam (Fin.rev i) := by funext i; rw [e]; simp
  subst hl
  unfold infOf
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

end Conj2

theorem sum_singletons {α : Type} (l : List α) (f : α → ℂ) : (l.map fun k => ({f k} : Multiset ℂ)).sum = ((l.map f : List ℂ) : Multiset ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Multiset.singleton_add]

theorem bindCast (t : ℕ) : ((List.range t >>= fun a => pure (a : ℂ)) : List ℂ) = (List.range t).map (fun a : ℕ => (a : ℂ)) := by
  simp [List.map_eq_flatMap]

theorem range_rev (t : ℕ) (f : ℕ → ℂ) : (Multiset.range t).map (fun c => f (t - 1 - c)) = (Multiset.range t).map f := by
  have h := congrArg (fun l : List ℕ => ((l.map f : List ℂ) : Multiset ℂ)) (List.reverse_range' (s := 0) (n := t))
  simp only [List.map_reverse, Multiset.coe_reverse, List.map_map] at h
  rw [← List.range_eq_range'] at h
  simpa [Multiset.range, Function.comp_def] using h.symm

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open GlobalTheory.LiftRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.LiftInfRef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.GalLoc.PsiLvl

def PsiRead (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i true ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
        (D.ntw.emb0 i ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0))

theorem exists_theta_of_eq {D₀ : D7} {L : LocAll (lay0 D₀)} {D' : D7} (h : D' = withLoc L)
    (θ0 : ∀ kk : Fin 2, Multiplicative (ZMod ((withLoc L).host.g kk)) →* (↥(withLoc L).LL0)ˣ)
    (h0 : PsiRead (withLoc L) θ0) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ, HEq θ θ0 ∧ PsiRead D' θ := by
  subst h
  exact ⟨θ0, HEq.rfl, h0⟩

end GlobalTheory.GalLoc.PsiLvl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEnlargedHeckeSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSbLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_sb_raw (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (YS : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG (ratDatR Rl cG kKs hk) YS)
    (hX : NExpHeckeRowX Rl cG _ YS H fun _ => LinearMap.id) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hne : Nonempty D.ntw.Tw)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) :
    ∃ Sb' : Finset (PlE D.host), Sb ⊆ Sb' ∧ (∀ i, Sb' ⊆ D.ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low D Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd Rl cG kKs hk Sb' H.hL := by
  classical
  obtain ⟨i₀⟩ := hne
  refine ⟨(D.ntw.S0 i₀).filter (fun P => ∀ i, P ∈ D.ntw.S0 i), fun P hP => Finset.mem_filter.2 ⟨hSb i₀ hP, fun i => hSb i hP⟩,
    fun i P hP => (Finset.mem_filter.1 hP).2 i, ?_, ?_⟩
  · intro P hP
    have hall : ∀ i, P ∈ D.ntw.S0 i := by
      intro i
      rw [Nat.cast_mul, Nat.cast_mul] at hP
      rcases P.isPrime.mem_or_mem hP with h | h
      · exact hS02 i h
      · rcases P.isPrime.mem_or_mem h with h | h
        · exact D.ntw.placesOver_subset_exceptional i 0 h
        · exact D.ntw.placesOver_subset_exceptional i 1 h
    exact Finset.mem_filter.2 ⟨hall i₀, hall⟩
  · intro j k P α Rr h1 h2 hd x
    have hi' : ∃ i', P ∉ D.ntw.S0 i' := by
      by_contra hc
      push_neg at hc
      exact hd.offS (Finset.mem_filter.2 ⟨hc i₀, hc⟩)
    obtain ⟨i', hi'⟩ := hi'
    obtain ⟨-, -, -, -, hso, -, -, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i') Rl.Sb P (hS0c i') (hS02 i') (hS0b i') hd.split hi'
    have hj : (idxOf D j : ℕ) + 1 = j := by simp only [idxOf]; omega
    let y : (ratDatR Rl cG kKs hk).WL ((idxOf D j : ℕ) + 1) := (YS.fi (idxOf D j)).e.symm x
    have hy : (YS.fi (idxOf D j)).e y = x := LinearEquiv.apply_symm_apply _ _
    have key : ∀ n (hn : n = j) (z : (ratDatR Rl cG kKs hk).WL n), HEq z x → HEq (H.hL n k P z) (H.hL j k P x) := by
      intro n hn z hz
      subst hn
      rw [eq_of_heq hz]
    have h3 : HEq ((YS.fi (idxOf D j)).e (H.hL ((idxOf D j : ℕ) + 1) k P y)) (H.hL j k P x) :=
      (hfi _ _).trans (key _ hj y ((hy ▸ hfi _ y).symm))
    have ht := hX.tie (idxOf D j) k P hd.split hso ⟨i', hi'⟩ hd.odd hd.le α Rr hd.elt hd.reps y rfl
    rw [eq_of_heq h3, hy] at ht
    exact ht

end Raw

end GlobalTheory.HeckeSbLayer

namespace GlobalTheory.HeckeSbLayer

end GlobalTheory.HeckeSbLayer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MembersGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnderFixedSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceUnderFixed

theorem exists_splitPlace_under_plGw : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D → ∃ (k : Fin 2) (v : D.nd.PlG k) (s₀ : SplitPlace D.host.E), s₀.w = D.naut.plGw k v ∧ s₀.v = s.v := by
  intro D s hs
  obtain ⟨k, u, s₀, hv, hw⟩ := GlobalTheory.FormInner.exists_split_of_gPl D s.v hs
  exact ⟨k, u, s₀, hw, hv⟩

end GlobalTheory.PlaceUnderFixed
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

theorem members_good (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (av : AVTied D M)
    (lv : LevelTied D M tup) (hT : TameAtG D tup) (i : D.nd.Loc) (P : D.naut.AV i) (s : SplitPlace D.host.E)
    (σ : IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS (av.S i P) s σ) :
    Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
  have hiso : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (av.S i P) := by
    have := hy
    rw [av.typeV i P] at this
    exact this
  have hty : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0 : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  have hjr := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  by_cases hg : s.v ∈ gPl D
  · obtain ⟨k, v, s₀, hw, hv⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
    obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := lv.uni i j hj k v s₀ hw
    have hfix := GlobalTheory.UniDepthZero.main D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J (M.loc i).χ
      (M.loc i).J_open s₀ D.R.r ψ₀ ξ hU hψ (hT i j k v s₀ ξ hw hc) _ hiso hty hf0 s hv.symm σ hσ
    exact good_of_fixed_KOne hZ (GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg) _ hfix
  by_cases hp : s.v ∈ paraPl D tup i j
  · obtain ⟨s₀, ξ, hv, -, hP⟩ := lv.para i j hj s.v hp
    exact good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open s₀ D.R.r ξ hP _ hiso hty hf0 s hv.symm σ hσ)
  · have hB : s.v ∉ gPl D ∪ paraPl D tup i j := fun h => h.elim hg hp
    exact good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open _ (lv.hyp i j hj) _ hiso hty hf0 s hB σ hσ)

end GlobalTheory.AVGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead

open GlobalTheory.TwistGood

theorem twistOf_good (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X) (hρ : ρ.Good)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (e : X.Ok i k →+* ℂ) (hψ : Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ) :
    (twistOf ρ.rc e (ρ.ch i) Q ψ).Good ∧ (ρ.B i j b).admitted (twistOf ρ.rc e (ρ.ch i) Q ψ).Q := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map e.toMonoidHom)
  have hkey : charOf ρ.rc e ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm⟩
  show (⟨half (ρ.ch i) Q, charOf ρ.rc e ψ, resOf (charOf ρ.rc e ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
    (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
    exact h3.mono (Finset.subset_union_right.trans h2)
  · intro P hP hl
    exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
  · intro v hv hnc B hB σ hσ
    have hvQ : v ∉ Q := by
      intro hvQ
      by_cases hc : v ∈ ρ.ch i
      · exact hv (mem_half.2 ⟨hvQ, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
        have hne := ne_of_split (hsplit v hvQ) hv'
        have hv'c : v' ∈ ρ.ch i := by
          by_contra h
          exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
        exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : ψ σ = 1 := by
      by_contra h
      exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, h1, map_one]

theorem twVia_good : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  intro D c w ρ hρ hψ j ι
  obtain ⟨h1, h2⟩ := twistOf_good D D.nd D.ntw ρ hρ (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (viaOk ι) hψ
  refine ⟨h1, h2, fun τ => ⟨rfl, fun x => ?_⟩⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l (c.twI w) ^ (c.k' w) ≠ 0 := pow_ne_zero _ (D.ntw.lPrime (c.twI w)).out.ne_zero
  have hp : chr c w σ ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 :=
      Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  change ((charOf ρ.rc (viaOk ((τ : ℂ →+* ℂ).comp ι)) (chr c w) x : Circle) : ℂ) =
    τ ((charOf ρ.rc (viaOk ι) (chr c w) x : Circle) : ℂ)
  rw [charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp, charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp]
  rfl

end GlobalTheory.PlaceRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosen_twist_via_embedding_good_conjugate : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  first | exact @GlobalTheory.PlaceRead.twVia_good | exact GlobalTheory.PlaceRead.twVia_good | (intros; apply GlobalTheory.PlaceRead.twVia_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLattice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceIndep

theorem sum_dual_smul_eq_zero {W ι I : Type} [AddCommGroup W] [Module ℂ W] (F : Subfield ℂ) {b : ι → W}
    (hb : LinearIndependent ℂ b) {v : I → W} (hv : ∀ a, v a ∈ Submodule.span F (Set.range b)) (s : Finset I) (c : I → ℂ)
    (h : ∑ a ∈ s, c a • v a = 0) (φ : Module.Dual F ℂ) : ∑ a ∈ s, φ (c a) • v a = 0 := by
  classical
  choose g hg using fun a => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv a)
  set t := s.biUnion fun a => (g a).support with ht
  have hv' : ∀ a ∈ s, v a = ∑ k ∈ t, g a k • b k := fun a ha => by
    rw [← hg a]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun a => (g a).support) ha) _ fun _ _ => zero_smul _ _
  have h1 : ∑ k ∈ t, (∑ a ∈ s, g a k • c a) • b k = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv' a ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_assoc, smul_comm]
  have h2 := linearIndependent_iff'.1 hb t _ h1
  rw [Finset.sum_congr rfl fun a ha => by rw [hv' a ha, Finset.smul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have h3 := congrArg φ (h2 k hk)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h3
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, Finset.sum_congr rfl fun a _ => by rw [mul_comm, ← smul_eq_mul, ← map_smul], h3, zero_smul]

theorem coefLatFn_mem_span {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {F : Subfield ℂ} (hF : O ≤ F.toSubring)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {φ : GLR D n → ℂ}
    (h : φ ∈ coefLatFn σ emb O lam M) :
    φ ∈ Submodule.span F (Set.range fun k => HarmLattice.cf lam (GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k))) := by
  have hσ : ∀ x : K, σ x ∈ F := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    exact div_mem (hF (hc.int a)) (hF (hc.int b))
  induction h using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨G, -, rfl⟩ := h
    rw [HarmLattice.coefFn_eq]
    have hG : G ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hG using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a G _ h1 =>
      rw [LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hσ a⟩ : F) h1
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c.1, hF c.2⟩ : F) h1

theorem linearIndependent_complex : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  intro D S T B hB K _ _ σ emb O hc F hF I f hf hli
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hcf : Function.Injective (HarmLattice.cf B.w.lam) :=
    (injective_iff_map_eq_zero _).2 fun G hG => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D _ B.w.lam G fun x => congrFun hG x)
  have hb := (GlobalTheory.CoefModel.linearIndependent_mapVV σ B.w.lam).map' (HarmLattice.cf B.w.lam) (LinearMap.ker_eq_bot.2 hcf)
  refine linearIndependent_iff'.2 fun s c h a ha => (Module.forall_dual_apply_eq_zero_iff F (c a)).1 fun φ => ?_
  refine linearIndependent_iff'.1 hli s (fun a => φ (c a)) (funext fun y => ?_) a ha
  refine GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ ?_ ?_
  · rw [Finset.sum_apply]
    exact sum_mem fun a _ => Submodule.smul_mem _ (φ (c a) : ℂ) (hf a y).1
  · have h0 := congrArg (harmFn T.rank B.w B.F.BS) (congrFun h y)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at h0
    simp only [Pi.smul_apply, map_smul] at h0
    have := sum_dual_smul_eq_zero F hb (fun a => coefLatFn_mem_span hc hF B.w.lam _ (hf a y).2) s c h0 φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun a _ => (harmFn T.rank B.w B.F.BS).map_smul (φ (c a) : ℂ) (f a y)

end GlobalTheory.PlaceIndep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.PlaceIndep.linearIndependent_complex | exact GlobalTheory.PlaceIndep.linearIndependent_complex | (intros; apply GlobalTheory.PlaceIndep.linearIndependent_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.NonSplitLevel

theorem comp_swapCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (Q : HeightOneSpectrum (𝓞 E))
    (x y : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2)
    (e : Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) x =
      Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) y) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm x) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm y) := by
  subst h
  have key : ∀ z : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast (rfl : F1 = F1)).symm z) =
        Algebra.TensorProduct.comm F1 E _
          (Algebra.TensorProduct.map (AlgHom.id F1 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, key, e]

variable {D : D7}

theorem projV_eq_one {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) (κ : GAf D.host.E n) (Q : PlE D.host)
    (hκ : (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (compAt D.host.E (HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) Q)) = 1) :
    GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ) = 1 := by
  classical
  obtain ⟨⟨β, β', h1, -, hβ⟩, -⟩ := hP
  let g := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F))) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hK : ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (swapCast hF).symm).map g = 1 := by
    ext i j
    have e2 := congrFun (congrFun hκ i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.map_apply, Matrix.map_apply]
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · exact (comp_swapCast hF Q _ 1 (e2.trans (map_one _).symm)).trans (by rw [map_one, map_one])
    · exact (comp_swapCast hF Q _ 0 (e2.trans (map_zero _).symm)).trans (by rw [map_zero, map_zero])
  refine GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig V.gram (Units.ext ?_)
  rw [MonoidHom.map_one, Units.val_one]
  have e1 : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ))).1 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map g :=
    Matrix.ext fun i j => (GlobalTheory.FinZeta.LevelOff.evalV_finPart (Q.under (𝓞 D.host.F)) _).symm
  rw [e1, hβ κ, Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero g) (map_one g)]

theorem split_of_not_conj {Q : PlE D.host} (h : ¬ Formalism.IndefR.Lev.IsConjPl Q Q) : IsSplitPl D.host Q := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  have e : star (c : D.host.E) = D.host.conj c := by
    apply D.host.φ₀.injective
    have := D.host.isCMField_hostE
    exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ _).trans
      (D.host.conjE_apply D.host.φ₀ _).symm
  exact ⟨c, hc, fun y hy hyQ => h y hyQ (hy.trans e.symm)⟩

theorem mem_level {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsSplitPl D.host PP) {w' : PlE D.host} (hw : ¬ IsSplitPl D.host w')
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (hT : TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w'} κ) :
    P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1 := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    refine projV_eq_one hP κ PP (hT _ fun e => ?_)
    have e' : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP =
        HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' := e
    exact GlobalTheory.SphNonSplit.not_split_of_overPl D (w := w') (w' := PP)
      (v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w') rfl
      (congrArg HeightOneSpectrum.asIdeal e') hw (hL PP hPP)
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hred, Units.val_one]

theorem lift_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP w' hw κ hU hT => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  refine mem_level hP hc _ (fun PP hPP => ?_) hw hU hT
  rcases hPP with h | h
  · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
    exact GlobalTheory.SphNonSplit.split_of_over_g _ k (GlobalTheory.Mem.TypePl.div_over _ hk)
  · exact split_of_not_conj ((hlev.Q_pl _ PP h).2 PP h)

end GlobalTheory.NonSplitLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_nonsplit_maxCompact_in_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  first | exact @GlobalTheory.NonSplitLevel.lift_level | exact GlobalTheory.NonSplitLevel.lift_level | (intros; apply GlobalTheory.NonSplitLevel.lift_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceFix

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

end GlobalTheory.PlaceFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)

theorem GlobalTheory.PlaceRead.evaluates_of_lunif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : Formalism.L2.Pj.CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl
end

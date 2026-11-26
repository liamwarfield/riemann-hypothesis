module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.BasicNotions.TH

namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement

theorem stdFrame_iff {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) :
    R3.StdFrame hF P ↔ GlobalTheory.NJoin.StdFrame hF P := by
  have key : ∀ {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2),
      R3.swapCast h = principalLevelFrame.tensCastR h := by
    intro E _ _ F1 F2 h
    subst h
    rfl
  unfold R3.StdFrame GlobalTheory.NJoin.StdFrame principalLevelFrame.StdPsi
  rw [key hF]


end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameBlockDiagonal

theorem rankV (D : D7) (k : Fin D.R.m) : (Vc D k).rank = D.R.nV := by
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) k.2]

def IsBlockDiagonalWithIdentity {K : Type} [CommRing K] {n r : ℕ} (x : GL (Fin r) K) (y : GL (Fin n) K) : Prop :=
  ∀ a b : Fin n, y.val a b =
    if h : a.val < r ∧ b.val < r then x.val ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then 1 else 0

end GlobalTheory.FrameBlockDiagonal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.TypesAt

theorem typesTrue_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  have h1 := t.r.z.lev.C
  have hg := t.grp
  rw [h1]
  have h2 := w.C_eq
  rw [h2]
  exact hg

end GlobalTheory.HeightCounting.Up.TypesAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.OPinAt

theorem mtInput_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (h : MtInput D M tup Q) : MtInput (withLoc L) (mtL L M) tup Q :=
  ⟨h.prod, h.para, h.uni, h.hyp, h.wt, h.rat, h.int, h.full⟩

theorem classSum_loc_of_sumTw {D : D7} {M : MtFam D} (h : SumTw D M) (i : D.nd.Loc) :
    GlobalTheory.CoefDuty.ClassSum (M.loc i) := by
  have e := D.nd.mu_w i
  have hs := h (D.nd.w i) (D.nd.w_tw i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2
  unfold MtFam.loc
  rw [e]
  exact hs

end GlobalTheory.HeightCounting.Up.OPinAt


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReading
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReading
namespace GlobalTheory

open Module

theorem descent_joint_eigen : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  classical
  intro K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv
  set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM
  have mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ := by
    intro S hS
    exact iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl
  have key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K,
      (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ →
      e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ := by
    intro S S'' hS k hk c hc v hv
    have hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v) := by
      simp [map_sub, hT k hk, LinearMap.map_smulₛₗ]
    rw [hrw]
    suffices h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv
    refine iSup₂_le fun σ hσ w hw => ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hPart σ (hS hσ) k hk w hw, ← sub_smul]
    by_cases h : σ ∈ S''
    · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))
    · rw [hc σ hσ h, sub_self, zero_smul]; exact Submodule.zero_mem _
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M := by
    intro n
    induction n with
    | zero =>
      intro S hS hSs v hv
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv
      have hvG : v ∈ G := hG v (by rw [hv]; exact Submodule.zero_mem _)
      rw [hinj v hvG hv]; exact Submodule.zero_mem _
    | succ n ih =>
      intro S hS hSs v hv
      rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
      · exact ih S (by simp [hS0]) hSs v hv
      by_cases hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k
      · have hvG : v ∈ G := hG v (mono S hSs hv)
        have heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k) := by
          refine Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_
          have h0 := key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv
          simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0
          have hmG : T k v - lam a k • v ∈ G := hG _ (by rw [h0]; exact Submodule.zero_mem _)
          have := hinj _ hmG h0
          rw [Module.End.mem_eigenspace_iff]
          exact sub_eq_zero.mp this
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))
      · push_neg at hall
        obtain ⟨b, hb, k, hk, hne⟩ := hall
        have hcb := Finset.card_erase_of_mem hb
        have hca := Finset.card_erase_of_mem ha
        have hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s := fun x y hy => hSs (Finset.mem_of_mem_erase hy)
        have h1 := ih (S.erase b) (by omega) (hsub b) _
          (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have h2 := ih (S.erase a) (by omega) (hsub a) _
          (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v)) := by
          rw [sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]
        rw [hv']; exact M.smul_mem _ (M.sub_mem h1 h2)

  have hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ := hv
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv2
  have hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ :=
    iSup₂_le fun σ hσ => iSup_le fun hs =>
      le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl
  exact main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReadingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_joint_eigenvectors_complex_reading : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  first | exact @GlobalTheory.descent_joint_eigen | exact GlobalTheory.descent_joint_eigen | (intros; apply GlobalTheory.descent_joint_eigen <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem spanC_core (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (htie : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ v : (ratDatR R cG kKs hk).WL j, v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j))
    (hinj : ∀ i, Function.Injective (iotaR R i))
    (hhk : ∀ (i : Fin D.R.m) (k : ℕ) (Pl : PlE D.host), 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host Pl → Pl ∉ Sb →
      ∃ α Rr, HkDat R Sb i k Pl α Rr)
    (hRd : HeckeRd R cG kKs hk Sb hL) (hEig : EigAd Y Sb eig) :
    SpanC (ratDatR R cG kKs hk) Sb θ hL eig := by
  intro j hj1 hj2
  classical
  have hjj : ((idxOf D j : Fin D.R.m) : ℕ) + 1 = j := by
    show min (j - 1) (D.R.m - 1) + 1 = j
    omega
  have hsg : ∀ c : D.what₂.LL, D.what₂.embLL c = sg0 D A3.A c := fun c =>
    (congrArg (fun g : D.what₂.LL →+* ℂ => g c) (GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL R)).symm
  let I : Set (ℕ × PlE D.host) := {t | 1 ≤ t.1 ∧ t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb}
  have ex : ∀ t : I, ∃ α Rr, HkDat R Sb (idxOf D j) t.1.1 t.1.2 α Rr := fun t =>
    hhk (idxOf D j) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  choose α Rr hD using ex
  let T' : ℕ × PlE D.host → Module.End ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun t =>
    if h : t ∈ I then hkNorm R (idxOf D j) t.1 t.2 • Formalism.IndefR.Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) (Rr ⟨t, h⟩)
    else 0
  let Part : D.what₂.FT → Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun σ =>
    (D.what₂.isot ((idxOf D j : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y (idxOf D j))
  let s : Set D.what₂.FT := {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}
  have hT : ∀ t ∈ I, ∀ u : Fin (R.nW (idxOf D j)) → D.what₂.LL,
      iotaR R (idxOf D j) (hL j t.1 t.2 u) = T' t (iotaR R (idxOf D j) u) := by
    intro t ht u
    simp only [T', dif_pos ht, LinearMap.smul_apply, iotaR_apply]
    exact hRd j t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) hj1 hj2 (hD ⟨t, ht⟩) u
  have hPa : ∀ σ ∈ s, ∀ t ∈ I, ∀ z ∈ Part σ, T' t z = sg0 D A3.A ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL) • z := by
    rintro σ hσ t ht _ ⟨y, hy, rfl⟩
    simp only [T', dif_pos ht, LinearMap.smul_apply]
    have h1 := hEig (idxOf D j) σ t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) (hD ⟨t, ht⟩) hσ.2 y hy
    have h2 : eig ((idxOf D j : ℕ) + 1) σ t.1 t.2 = eig j σ t.1 t.2 := by rw [hjj]
    rw [h2, hsg] at h1
    exact h1
  have hGa : ∀ u, iotaR R (idxOf D j) u ∈ ⨆ σ ∈ s, Part σ → u ∈ goodL D (ratDatR R cG kKs hk) θ j := by
    intro u hu
    refine (htie j hj1 hj2 u).2 ?_
    have hle : (⨆ σ ∈ s, Part σ) ≤ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) :=
      iSup₂_le fun σ _ => Submodule.map_le_iff_le_comap.2 fun y _ => readW_mem_goodW Y (idxOf D j) y
    exact hle hu
  intro v hv
  have hv' : iotaR R (idxOf D j) v ∈ ⨆ σ ∈ s, Part σ :=
    goodW_le_parts Y hI hG (idxOf D j) j hjj ((htie j hj1 hj2 v).1 hv)
  have hd := GlobalTheory.T.descent_joint_eigenvectors_complex_reading (sg0 D A3.A) (iotaR R (idxOf D j)) (goodL D (ratDatR R cG kKs hk) θ j)
    (fun u _ h0 => hinj (idxOf D j) (h0.trans (map_zero _).symm)) (fun t => hL j t.1 t.2) T' I hT Part s
    (fun σ t => ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) hPa hGa v hv'
  have hle : (⨆ σ ∈ s, goodL D (ratDatR R cG kKs hk) θ j ⊓ ⨅ t ∈ I,
      Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) ≤
      ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D (ratDatR R cG kKs hk) θ j ⊓
        ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb),
          Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL) :=
    iSup₂_mono fun σ _ => inf_le_inf_left _ (le_iInf fun k => le_iInf fun Pl => le_iInf fun h =>
      iInf₂_le (f := fun t (_ : t ∈ I) => Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL))
        (k, Pl) h)
  exact hle hd

end Core

end GlobalTheory.EigSpanDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
  {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem IsMetricOn.mContDiffAt_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    MContDiffAt 2 (fun u => H A (c.e.symm u) τ) (c.e y) := by
  intro a b
  have hy'' : c.e.symm (c.e y) = y := c.e.left_inv hc
  have hsm := hM.smooth y hy A hA
  have hevent {f : CxPts X.str σ → ℝ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
    obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
    have hW := (isOpen_ptsIn W).mem_nhds h₁
    have hc : ContinuousAt (fun z a => ev X.str σ W (g a) z) y :=
      continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
    filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
    exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩
  have hre := hevent (hsm τ a b).1
  have him := hevent (hsm τ a b).2
  have hn : ∀ {f : CxPts X.str σ → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt f z) → ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) := by
    intro f hf
    have hs : c.e.target ∩ c.e.symm ⁻¹' {z | CInfAt f z} ∈ 𝓝 (c.e y) := by
      refine Filter.inter_mem (c.e.open_target.mem_nhds (c.e.map_source hc)) ?_
      exact (c.e.continuousAt_symm (c.e.map_source hc)).preimage_mem_nhds (hy''.symm ▸ hf)
    exact ((contDiffOn_chart (fun z hz => hz) c).contDiffAt hs).of_le (by norm_cast)
  have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  exact (Complex.re_add_im _).symm

theorem IsMetricOn.isUnit_det_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    IsUnit (H A (c.e.symm (c.e y)) τ).det := by
  rw [c.e.left_inv hc]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hM.posDef y hy A hA τ).isUnit

theorem IsMetricOn.chernTop_frame [Finite ι] (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A A' : Mat m X.Fn}
    (hA : A ∈ E.S (under y)) (hA' : A' ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) = chernTop R (fun v => H A' (c.e.symm v)) (c.e y) := by
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A * A'⁻¹) := (Fr.mem_iff hA').1 hA
  refine GlobalTheory.PointChern.chernTop_changeFrame R _ _ (fun w => (A * A'⁻¹).map (ratVal · (c.e.symm w))) (fun _ => 1) _
    (fun _ => one_pos) (fun τ i j => GlobalTheory.FrameLift.analyticAt_ratVal c hc (mem_O_ratOf.1 ((hP τ).1 i j)))
    (fun τ => ?_) (hM.mContDiffAt_chart hy c hc hA') (hM.isUnit_det_chart hy c hc hA') ?_
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    simp only [c.e.left_inv hc]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne τ).isUnit
  · have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    filter_upwards [(c.e.tendsto_symm hc).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))] with w hw τ
    rw [Complex.ofReal_one, one_smul]
    exact hM.trans _ hw.1 A' hw.2.2 A hw.2.1 τ

theorem IsMetricOn.chernTop_chart (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c c' : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) (hc' : y ∈ c'.e.source)
    {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
      ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A (c'.e.symm v)) (c'.e y) := by
  let K : V X.dim → Mat m ℂ := fun v => H A (c'.e.symm v)
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hc hc'
  have hφ : AnalyticAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo_trans c') (ho.mem_nhds hm)
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hc)
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (c'.e y) := hM.mContDiffAt_chart hy c' hc' hA
  have hKu : ∀ τ, IsUnit (K (c'.e y) τ).det := hM.isUnit_det_chart hy c' hc' hA
  have key := GlobalTheory.ChernPull.chernTop_comp R K (c'.e ∘ c.e.symm) (c.e y) hφ (e₂ ▸ hK2) (e₂ ▸ hKu)
  have hg : (fun v => H A (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun w => K ((c'.e ∘ c.e.symm) w) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [K, Function.comp_apply, c'.e.left_inv hw.2]
  have hcongr : chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
      chernTop R (fun w => K ((c'.e ∘ c.e.symm) w)) (c.e y) := by
    have hh : ∀ x : ι × ℕ, chernPoly (fun u => H A (c.e.symm u) x.1) (c.e y) x.2 =
        chernPoly (fun u => K ((c'.e ∘ c.e.symm) u) x.1) (c.e y) x.2 := by
      intro x
      unfold chernPoly curvPoly
      simp only [curv_congr (hg.mono fun u hu => congrFun hu x.1)]
    simp only [chernTop, hh]
  rw [hcongr, key, e₂, transDet, Complex.sq_norm]

end GlobalTheory.GoodMetric

theorem GlobalTheory.GoodMetric.chernTop_frame_chart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  intro F _ σ X ι _ m E O H hM R y hy c c' hc hc' A A' hA hA'
  rw [hM.chernTop_frame R hy c hc hA hA', hM.chernTop_chart R hy c c' hc hc' hA']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactorStatement
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  first | exact @GlobalTheory.GoodMetric.chernTop_frame_chart_trans | exact GlobalTheory.GoodMetric.chernTop_frame_chart_trans | (intros; apply GlobalTheory.GoodMetric.chernTop_frame_chart_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
section -- merged from Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotExistsExponentConditionCard
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.ToricDenomCheck
variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem conj_conj' {R : Ranks} (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem isConj_symm {R : Ranks} {H : Host R} {P P' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H P P') : IsConjPl H P' P :=
  fun x y hy => (h y x (by rw [hy, conj_conj'])).symm

end GlobalTheory.ToricDenomCheck
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdXSubCScaleMemLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLift

open Polynomial

theorem prod_X_sub_C_scale_mem_lifts {K : Type} [Field K] (f : K →+* ℂ) (M : Multiset ℂ) (y : K)
    (hy : f y ≠ 0) (h : (M.map (fun α => X - C α)).prod ∈ Polynomial.lifts f) :
    ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod ∈ Polynomial.lifts f := by
  set q : ℂ[X] := C (f y)⁻¹ * X with hq
  have key : ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod =
      C (f y) ^ Multiset.card M * ((M.map (fun α => X - C α)).prod).comp q := by
    clear h
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih, mul_comp]
      have e1 : (X - C a).comp q = C (f y)⁻¹ * X - C a := by simp [hq]
      have e2 : X - C (a * f y) = C (f y) * (C (f y)⁻¹ * X - C a) := by
        rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy, C_1, one_mul, ← C_mul, mul_comm (f y) a]
      rw [e1, e2]; ring
  rw [key]
  refine mul_mem (pow_mem (Polynomial.C_mem_lifts f y) _) ?_
  rw [Polynomial.lifts_iff_set_range] at h ⊢
  obtain ⟨p, hp⟩ := h
  refine ⟨p.comp (C y⁻¹ * X), ?_⟩
  rw [Polynomial.map_comp, hp, hq]
  simp [map_inv₀]

end GlobalTheory.TwistLift

namespace GlobalTheory.TwistLift

open Polynomial

theorem galPol_lifts_tw_etaTinv : ∀ (D : D7) (cf : CharFrame D), GlobalTheory.HeightCounting.CharSide D cf → ValLL0 D cf → ∀ π : D.naut.CG D.R.r, (∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D)) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf hC hV π hπ
  obtain ⟨k, hk⟩ := D.R.t_odd
  filter_upwards [hπ, D.naut.locG_unr_ae π] with w hw hu
  have hUe : cf.eta.UnrAt w := by
    have h1 := (hC.unr_iff D.naut.etaT w).1 (D.naut.etaT_unr w)
    rwa [hC.etaT] at h1
  have hFe : D.naut.frobEig (D.naut.locG D.naut.etaT w) = {((cf.eta.val w : ℂ))⁻¹} := by
    have h1 := hC.frob D.naut.etaT w (by rw [hC.etaT]; exact hUe)
    rw [h1, hC.etaT]; simp
  have hFi : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(cf.eta.val w : ℂ)} := by
    rw [(D.naut.etaTinv_def w).2, hFe]; simp
  have hUi : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hD1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  obtain ⟨y, hy⟩ := hV.eta w hUe
  have hNv : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ≠ 0 := by
    rw [hNv, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  set N : ℂ := ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) with hNdef
  set lam : D.LL0 := y * (((Formalism.ConjugateSelfDual.normV w : ℕ) : D.LL0) ^ k)⁻¹ with hlamdef
  have hlam : embLL0 D lam = (cf.eta.val w : ℂ) * N ^ (-(1 / 2 : ℂ)) * (N ^ k)⁻¹ := by
    rw [hlamdef, map_mul, map_inv₀, map_pow, map_natCast, hy, Formalism.L2.Host.HChar.valTw, hNdef, hNv]
    push_cast; ring
  have hlam0 : embLL0 D lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (inv_ne_zero (pow_ne_zero _ hN))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hmul : D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) =
      (D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map (fun x => x * embLL0 D lam) := by
    rw [D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hD1 hu hUi),
      D.naut.frobEig_char _ _ _ hu hUi hD1 hFi, D.naut.frobEig_tw _ _ hu, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp only [Function.comp_apply]
    have hs : (((1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) + (-(1 / 2 : ℂ)) + (-(k : ℂ)) := by
      have e : D.R.nV = D.R.r + D.R.t := rfl
      rw [e, hk]; push_cast; ring
    rw [hlam, ← hNdef, hs, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN, Complex.cpow_neg (x := N) (y := (k : ℂ)),
      Complex.cpow_natCast]
    ring
  have hw' := hw
  simp only [galPol] at hw' ⊢
  rw [hmul]
  exact prod_X_sub_C_scale_mem_lifts (embLL0 D) _ lam hlam0 hw'

end GlobalTheory.TwistLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmMapMulConst
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrobSplit

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (s.map (fun x => x * c)).esymm k = c ^ k * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hk : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const',
    Multiset.prod_replicate, hk]
  ring

theorem galPol_lifts_ae : ∀ (D : D7) (cf : CharFrame D) (Rw : GlobalTheory.HeightCounting.RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), ValLL0 D cf → GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∀ π : D.naut.CG D.R.r, D.naut.csd π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) → ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf Rw Sb eig hV hE j hj1 hj2 σ hiso hgood π hcsd hloc
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  let j' : Fin D.R.m := ⟨j - 1, by omega⟩
  have hjj : (j' : ℕ) + 1 = j := by simp only [j']; omega
  have hfin : (bar ⁻¹' ((Sb : Set (PlE D.host)) ∪ {v | ¬ (cf.mu0 j').UnrAt v})).Finite :=
    (Sb.finite_toSet.union (GlobalTheory.Mem.UnrAe.finite_ramified _)).preimage hinj.injOn
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  by_contra hw'
  apply hw
  intro hsplit
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hw'
  obtain ⟨hSb, hunrμ⟩ := hw'
  obtain ⟨hc, -, hsp⟩ := hbar w
  have hPs : IsSplitPl D.host (bar w) := hsp hsplit
  have hE' := hE j' σ (by rw [hjj]; exact hiso) hgood (bar w) hPs hSb
  rw [hjj] at hE'
  obtain ⟨hunrP, heig⟩ := hE'
  rw [← hloc (bar w) hPs] at hunrP heig
  obtain ⟨hunrw, hfw⟩ := D.naut.csd_unr π (bar w) w hcsd (GlobalTheory.ToricDenomCheck.isConj_symm hc) hunrP
  have hfP : D.naut.frobEig (D.naut.locG π (bar w)) =
      (D.naut.frobEig (D.naut.locG π w)).map (fun x => x⁻¹) := by
    rw [hfw, Multiset.map_map]; simp
  have hcard : (D.naut.frobEig (D.naut.locG π w)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hunrw, D.naut.locG_dim]
  have hmemS : ∀ x, x ∈ (embLL0 D).fieldRange → x ∈ Set.range (embLL0 D) :=
    fun x h => (RingHom.mem_fieldRange).1 h
  have hNS : ∀ n : ℕ, (n : ℂ) ∈ (embLL0 D).fieldRange := fun n => natCast_mem _ n
  have hN0 : (Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.ConjPoly.normV_ne_zero (bar w)
  have hμ0 : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  obtain ⟨yμ, hyμ⟩ := hV.mu0 j' (bar w) hunrμ
  have hμS : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange :=
    ⟨yμ, by rw [hyμ]; simp [Formalism.L2.Host.HChar.valTw]⟩
  have hAk : ∀ k, 1 ≤ k → k ≤ D.R.r →
      (D.naut.frobEig (D.naut.locG π w)).esymm k ∈ (embLL0 D).fieldRange := by
    intro k hk1 hk2
    have h := heig k hk1 hk2
    rw [hfP, Multiset.map_map] at h
    have hfun : (fun a : ℂ => a⁻¹ * (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ (fun x : ℂ => x⁻¹) =
        fun x => x * ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
      funext x; simp [mul_assoc]
    rw [hfun, esymm_map_mul_const] at h
    have hd : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ≠ 0 := by
      simp [hμ0, hN0]
    have hdS : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∈ (embLL0 D).fieldRange :=
      Subfield.mul_mem _ (Subfield.inv_mem _ hμS) (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))
    have hpow : ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2)) ≠ 0 := pow_ne_zero _ hN0
    have heq : (D.naut.frobEig (D.naut.locG π w)).esymm k =
        D.what₂.embLL ↑(eig j σ k (bar w)) * ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2))⁻¹ *
          (((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
            ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ^ k)⁻¹ := by
      rw [h]; field_simp
    rw [heq]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ⟨eig j σ k (bar w), rfl⟩
      (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))) (Subfield.inv_mem _ (Subfield.pow_mem _ hdS _))
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Formalism.BasicNotions.Ranks.r]; omega⟩
  obtain ⟨q, hq⟩ := hr
  have hs : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) =
      ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹ := by
    have : ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) = -(q : ℂ) := by
      rw [hq]; push_cast; ring
    rw [this, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  unfold Formalism.MainNotions.N.galPol
  rw [D.naut.frobEig_tw _ _ hunrw, hs]
  have hBk : ∀ k, k ≤ D.R.r →
      ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).esymm k ∈
        (embLL0 D).fieldRange := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : Multiset.esymm ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)) 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [this]; exact Subfield.one_mem _
    rw [esymm_map_mul_const]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _)) _)
      (hAk k hk1 hk)
  have hBc : ((D.naut.frobEig (D.naut.locG π w)).map
      (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).card = D.R.r := by
    rw [Multiset.card_map, hcard]
  rcases le_or_gt n D.R.r with hn | hn
  · rw [Multiset.prod_X_sub_C_coeff _ (hBc.symm ▸ hn), hBc]
    exact hmemS _ (Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _)
      (hBk _ (by omega)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hBc]; exact hn)]
    exact ⟨0, map_zero _⟩

end GlobalTheory.CuspFrobSplit
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SCuspRows

theorem allSt_and' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)


end GlobalTheory.SCuspRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
open NumberField IsDedekindDomain Formalism.L2

noncomputable section

namespace GlobalTheory.HeckeSplitComp

open ReciprocityTheory.Aut

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  intro L _ _ _ s χ hχ
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L s
  have hlt : ∀ y, Valued.v (c y) < 1 ↔ Valued.v y < 1 := GlobalTheory.TypeBlockFix.v_map_lt_one_iff s.v s.w c hc
  have hle : ∀ y, Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := GlobalTheory.TypeBlockFix.v_map_le_one_iff s.v s.w c hc
  have heq1 : ∀ y, Valued.v y = 1 → Valued.v (c y) = 1 := by
    intro y hy
    refine le_antisymm ((hle y).2 hy.le) (not_lt.1 fun h => ?_)
    have := (hlt y).1 h
    rw [hy] at this
    exact lt_irrefl _ this
  refine ⟨(χ.loc s.w).comp (Units.map c.toRingHom.toMonoidHom), ⟨⟨1, fun u hu => ?_⟩, fun k => ?_⟩, ?_⟩
  · have hu1 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 :=
      lt_of_le_of_lt hu (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hv : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := 1)
        (y := (u : s.v.adicCompletion (maximalRealSubfield L))) (by rw [map_one]; exact hu1)
      rwa [map_one] at this
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = 1
    refine hχ _ (heq1 _ hv) ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) - 1 =
        c ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]
    exact le_exp_neg_one_of_lt_one ((hlt _).2 hu1)
  · show χ.loc s.w (Units.map c.toRingHom.toMonoidHom (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)) =
      χ.loc s.w (Formalism.L2.Host.atFin s.w k)
    congr 1
    ext
    simp [Formalism.L2.Host.atFin, hci]
  · intro u a k hka hu hua
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = χ.locK s.w k
    have hia : Valued.v (s.i (a : L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := (u : s.v.adicCompletion (maximalRealSubfield L)))
        (y := s.i (a : L)) (by rw [Valuation.map_sub_swap, hu]; exact hua)
      rw [this, hu]
    have hk : s.w.valuation L (k : L) = 1 := by
      have h1 := heq1 _ hia
      rw [hci, ← hka] at h1
      rwa [Formalism.UG.P.levelaf_valued_algebraMap] at h1
    refine GlobalTheory.LevMuDet.loc_eq_locK hχ hk ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) -
        algebraMap L _ (k : L) = c ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) := by
      rw [map_sub, hci, hka]; rfl
    rw [e]
    exact (hlt _).2 hua

end GlobalTheory.HeckeSplitComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponentStatement
open NumberField IsDedekindDomain Formalism.L2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_heckeCharacter_split_place_local_component : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  first | exact @GlobalTheory.HeckeSplitComp.main | exact GlobalTheory.HeckeSplitComp.main | (intros; apply GlobalTheory.HeckeSplitComp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem exists_starSubdivision : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := GlobalTheory.T.exists_starSubdivision_function_integral_strictly_concave E H q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.starSubdivision_function_linearOn_cells E H q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell H.bar (starFun H.bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf H.bar q ψ w (starFun H.bar ψ w K D) := GlobalTheory.T.isStarOf_of_cells_starCone_or_centreless E H q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun H.bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth H.bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun H.bar ψ w K D, GlobalTheory.T.isPolyFan_of_starSubdivision_cells E H q ψ w _ hψ hW hstar hint hpos,
    isTwInv_starFun H htψ (GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant E H ψ w htψ htw) K D, GlobalTheory.T.starSubdivision_subordinate_to_fan _ H.bar q ψ w _ hstar, hstar⟩

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.exists_starSubdivision | exact GlobalTheory.PolFan.exists_starSubdivision | (intros; apply GlobalTheory.PolFan.exists_starSubdivision <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBall
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBall
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

theorem combMat_mul_left {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (b * ε) = combMat l ε * bᵀ.map (Rat.cast : ℚ → ℂ) := by
  have h := combMat_add_mul l ε 0 bᵀ
  have h0 : combMat l (0 : Matrix (Fin g) (Fin r) ℚ) = 0 := by
    ext k j; simp [combMat]
  rwa [h0, zero_add, zero_add, Matrix.transpose_transpose] at h

theorem combMat_add {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) :
    combMat l (ε + φ) = combMat l ε + combMat l φ := by
  ext k j
  simp [combMat, add_mul, Finset.sum_add_distrib]

theorem isUnit_det_combMat_on_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  intro n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ B hD hζ hstd hlam hc hdl hP hτ hB hper z hz
  choose I hI using hstd
  let sel : Matrix (Fin g) (Fin r₀) ℚ := Matrix.of fun j i => if i = I j then 1 else 0
  let Dl : Matrix (Fin g) (Fin g) ℂ := (sel * dl)ᵀ.map (Rat.cast : ℚ → ℂ)
  let G : Matrix (Fin g) (Fin g) ℂ := (sel * gm)ᵀ.map (Rat.cast : ℚ → ℂ)
  have hsel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, combMat (ζ z) sel = 1 := by
    intro z hz
    ext k j
    have h1 : combMat (ζ z) sel k j = ζ z (I j) k := by
      simp only [combMat, sel, Matrix.of_apply]
      rw [Finset.sum_eq_single (I j)]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    rw [h1, hI j z hz, Matrix.one_apply, Pi.single_apply]
  have hBD : ∀ k, (B k).map (Int.cast : ℤ → ℂ) * Dl = 0 := by
    intro k
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Dl, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < rk
    · simp [hdl _ l hl]
    · simp [hB k i l (Or.inr (not_lt.mp hl))]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPc : ContinuousOn (fun z => combMat (ζ z) α) (Metric.ball (0 : Fin n → ℂ) 1) := by
    refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => ?_
    simp only [combMat, Matrix.of_apply]
    refine continuousOn_finsetSum _ fun m _ => continuousOn_const.mul ?_
    exact continuousOn_pi.1 (continuousOn_pi.1 hζ.continuousOn m) k
  have hτc : ContinuousOn τ₀ (Metric.ball (0 : Fin n → ℂ) 1) :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => (hτ k i).continuousOn
  have hQ : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
      p.1 * (G + (D : ℂ)⁻¹ • (p.2 * Dl))) := by fun_prop
  have hQc : ContinuousOn (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl)))
      (Metric.ball (0 : Fin n → ℂ) 1) := by
    have h := hQ.comp_continuousOn (hPc.prodMk hτc)
    simpa only [Function.comp_def] using h
  have key := GlobalTheory.eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix (Fin g) (Fin g) ℂ)
    (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl))) (fun _ => 1) le_rfl
    hQc continuousOn_const (by
      intro s hs hb
      have h1 := hsel _ hb
      rw [combMat_comb _ _ c sel (hlam s hs), hc, Matrix.mul_add, ← Matrix.mul_assoc sel gm, ← Matrix.mul_assoc sel dl,
        combMat_add, combMat_mul_left, combMat_mul_left, ← combMat_comb _ _ c α (hlam s hs)] at h1
      have h2 := congrArg (fun T => T * Dl) (hper s hs hb)
      simp only [perTau, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, hBD, smul_zero, Finset.sum_const_zero,
        add_zero] at h2
      rw [← h2, smul_smul, inv_mul_cancel₀ hDc, one_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hP s hs), Matrix.one_mul]
      exact h1) z hz
  exact Matrix.isUnit_det_of_right_inverse key

end GlobalTheory.PeriodFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBallStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  first | exact @GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball | exact GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball | (intros; apply GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball <;> assumption)
end
end

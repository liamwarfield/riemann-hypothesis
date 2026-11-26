module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPtsEqImage
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundImage
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovFund

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def reix (X : HidaSetting D) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) ≃ᵐ X.B.I.Ginf :=
  MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm

theorem reix_apply (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (τ : D.what₂.Tau) :
    reix X p (vOf X τ) = p τ := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm p τ

theorem reix_symm (x : X.B.I.Ginf) (τ : D.what₂.Tau) : (reix X).symm x τ = x (vOf X τ) := by
  conv_rhs => rw [← (reix X).apply_symm_apply x]
  exact (reix_apply _ τ).symm

theorem trI_apply (x : X.B.I.Ginf) (τ : D.what₂.Tau) : trI C x τ = GlobalTheory.PullbackComparison.eM C τ (x (vOf X τ)) := rfl

theorem trI_emb : MeasurableEmbedding (trI C) := by
  choose g hg hgf using fun τ : D.what₂.Tau =>
    (GlobalTheory.PullbackComparison.eM_emb C τ).exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun m => reix X (fun τ => g τ (m τ))) ?_ ?_ ?_ ?_
  · exact Measurable.of_eval fun τ =>
      (GlobalTheory.PullbackComparison.eM_emb C τ).measurable.comp (measurable_pi_apply (vOf X τ))
  · have hR : Set.range (trI C) = Set.univ.pi fun τ => Set.range (GlobalTheory.PullbackComparison.eM C τ) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩ τ _
        exact ⟨x (vOf X τ), (trI_apply C x τ).symm⟩
      · intro hm
        choose a ha using fun τ => hm τ (Set.mem_univ τ)
        refine ⟨reix X a, funext fun τ => ?_⟩
        rw [trI_apply, reix_apply, ha]
    rw [hR]
    exact MeasurableSet.univ_pi fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurableSet_range
  · exact (reix X).measurable.comp
      (Measurable.of_eval fun τ => (hg τ).comp (measurable_pi_apply τ))
  · intro x
    have h1 : (fun τ => g τ (trI C x τ)) = (reix X).symm x := by
      funext τ
      rw [trI_apply, reix_symm]
      exact congrFun (hgf τ) _
    simp only [h1, MeasurableEquiv.apply_symm_apply]

theorem trI_mul (q y : X.B.I.Ginf) : GlobalTheory.DegVol.mulP (trI C q) (trI C y) = trI C (q * y) := by
  funext τ
  have hv : (q * y) (vOf X τ) = q (vOf X τ) * y (vOf X τ) := rfl
  rw [trI_apply C (q * y), hv, GlobalTheory.PullbackComparison.eM_mul]
  rfl

theorem exists_pre {Y : Full X} {u : D.what₂.Word} (t : GT Y u) {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hx : x ∈ GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) :
    ∃ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, trI C y = x := by
  have hr : ∀ τ, x τ ∈ Set.range (GlobalTheory.PullbackComparison.eM C τ) := fun τ =>
    GlobalTheory.PullbackComparison.uh_range C τ (hx τ).1.1
  choose a ha using hr
  refine ⟨reix X a, ?_, funext fun τ => ?_⟩
  · rw [GlobalTheory.PullbackComparison.rset_iff C t]
    intro τ
    rw [reix_apply, ha]
    exact hx τ
  · rw [trI_apply, reix_apply, ha]

theorem isFund_image : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (t : GT Y u) (K : Set X.B.I.Ginf), FundR t K → GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.TermOp.ROinf t) (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) (trI C '' K) := by
  intro D X Y u C t K hK
  refine ⟨(trI_emb C).measurableSet_image.2 hK.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_pre C t hx
  obtain ⟨q, ⟨hq, hqK⟩, huniq⟩ := hK.2 y hy
  refine ⟨trI C q, ⟨⟨q, hq, rfl⟩, ?_⟩, ?_⟩
  · rw [trI_mul]
    exact ⟨q * y, hqK, rfl⟩
  · rintro m ⟨⟨q', hq', rfl⟩, hm⟩
    rw [trI_mul] at hm
    obtain ⟨z, hz, hzq⟩ := hm
    have hzq' : z = q' * y := (trI_emb C).injective hzq
    rw [huniq q' ⟨hq', by rw [← hzq']; exact hz⟩]

end GlobalTheory.CovFund
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagToFrameOfNonzeroLevelIsotropicEq
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.StabRat
open Formalism.HermitianLatticeCounting.S6

section Conj
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

theorem xa_map {F G : FlagD H r} (g : V ≃ₗ[K] V) (he : ∀ a, G.e a = g (F.e a)) (a : ℕ) :
    G.Xa a = (F.Xa a).map (g : V →ₗ[K] V) := by
  unfold FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => he _

theorem inN_conj {F G : FlagD H r} (g : V ≃ₗ[K] V) (hg : ∀ x y, H.B (g x) (g y) = H.B x y)
    (he : ∀ a, G.e a = g (F.e a)) (n : V ≃ₗ[K] V) :
    G.InN (n : V →ₗ[K] V) ↔ F.InN ((g⁻¹ * n * g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hc : ∀ x, (g⁻¹ * n * g) x = g.symm (n (g x)) := fun x => rfl
  have hX := xa_map g he
  unfold FlagD.InN FlagD.X
  simp only [LinearEquiv.coe_coe, hc]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, (g⁻¹ * n * g).bijective, fun a => ?_, fun y hy => ?_⟩
    · rw [← hg (g.symm (n (g x))), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h1, hg]
    · have := h3 a
      rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
    · have := h4 (g y) fun a => by rw [he, hg, hy]
      rw [hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, n.bijective, fun a => ?_, fun y hy => ?_⟩
    · have := h1 (g.symm x) (g.symm y)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← hg (g.symm (n x)), ← hg (g.symm x)] at this
      simpa only [LinearEquiv.apply_symm_apply] using this
    · rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]
      exact h3 a
    · have hy' : ∀ a : Fin r, H.B (F.e a.castSucc) (g.symm y) = 0 := fun a => by
        rw [← hg, LinearEquiv.apply_symm_apply, ← he, hy]
      have := h4 (g.symm y) hy'
      rw [LinearEquiv.apply_symm_apply] at this
      rw [hX, Submodule.mem_map_equiv, map_sub]
      exact this

end Conj

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem frF_xa (F : FlagG S r T) (hT : T ≠ 0) (a : ℕ) : (frF F hT).Xa a = F.Xa a := by
  unfold FlagD.Xa FlagG.Xa
  congr 1
  exact Set.image_congr fun b _ => fv_cast F b

theorem flagToFrameOfNonzeroLevel_isotropic_eq (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [FlagD.X, frF_xa]
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

theorem inN_frF_iff (F : FlagG S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    (frF F hT).InN (n : S.V →ₗ[E] S.V) ↔ n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) ∧
      (∀ x ∈ orth S F.X, n x - x ∈ F.X) := by
  have he : ∀ a : Fin r, (frF F hT).e a.castSucc = F.e a := fv_cast F
  have hB : ∀ x y, (spH S).B x y = S.hT y x := fun _ _ => rfl
  unfold FlagD.InN
  simp only [LinearEquiv.coe_coe, frF_xa, flagToFrameOfNonzeroLevel_isotropic_eq, he, hB]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => h1 y x, fun j x hx => ?_, fun x hx => h4 x fun a => ?_⟩
    · have : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        have hb' : b.val < j + 1 := hb
        have hle : F.Xa b.val ≤ F.Xa j :=
          Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc (Nat.lt_succ_iff.1 hb'))
        exact hle (h3 b)
      exact this hx
    · have h0 : S.hT (F.e a) x = 0 := by
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
        exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
      rw [a_herm, h0, star_zero]
  · rintro ⟨h1, h3, h4⟩
    refine ⟨fun x y => h1 y x, n.bijective, fun a => ?_, fun y hy => h4 y ?_⟩
    · exact h3 a.val _ (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    · simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have : F.X ≤ LinearMap.ker (S.hT y) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, rfl⟩
        exact hy b
      rw [a_herm, LinearMap.mem_ker.1 (this hx), star_zero]

theorem mem_NLam_iff (Λ : Submodule (𝓞 E) S.V) (L : LFlag S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    n ∈ NLam Λ L ↔ (frF L.fl hT).InN (n : S.V →ₗ[E] S.V) ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  rw [inN_frF_iff]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c, d⟩, b⟩, fun ⟨⟨a, c, d⟩, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩

theorem fvec_mapLF (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T) (a : Fin (r + 1)) :
    (mapLF g L).fl.fvec a = g (L.fl.fvec a) := by
  rw [mapLF, dite_eq_left hg]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [fv_last, fv_last]; rfl
  · rw [fv_cast, fv_cast]; rfl

end Gen
end GlobalTheory.TypeAsm.StabRat

namespace GlobalTheory.TypeAsm
open StabRat GlobalTheory.DegAsm.AdaptInv

theorem gam_iff_nLam : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : Formalism.L2.SG.TermOp.GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS), AdT t N → ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ N.Gam t.lam ↔ (n ∈ NLam t.lam (lf D (X.Fu u)) ∧ t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u))) := by
  intro D large₂ X Y u _ t N hN n
  obtain ⟨-, h, h'⟩ := hN
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlam : t.lin • t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : N.F.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h) _, inN_of h _⟩
  have e2 : N.F'.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (Ft t).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h') _, inN_of h' _⟩
  have e3 := inN_conj (F := F0 X u) (G := Ft t) t.lin (fun x y => hiso y x)
    (fvec_mapLF t.lin hiso (lf D (X.Fu u))) n
  have hL : ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      m ∈ NLam Λ (lf D (X.Fu u)) ↔ (F0 X u).InN (m : (VS D).V →ₗ[D.host.E] (VS D).V) ∧ m • Λ = Λ :=
    fun Λ m => mem_NLam_iff Λ _ (tu_ne D u) m
  have e4 : (t.lin⁻¹ * n * t.lin) • t.lam' = t.lam' ↔ n • t.lam = t.lam := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff, hlam]
  rw [GlobalTheory.DegCnt.NF.Gam, Subgroup.mem_inf, GlobalTheory.UnipStab.mem_R, MulAction.mem_stabilizer_iff, e1, e2, e3, hL, hL, e4]
  tauto
end GlobalTheory.TypeAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundConjAndMeasure
noncomputable section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol.UnipConj
variable {k r : ℕ} {ι : Type}

theorem of_conjM (a : Mat k r) (x : Mt k r) : Matrix.of (conjM a x) = a * Matrix.of x * a⁻¹ := rfl

theorem conjM_lmulM {a : Mat k r} (ha : IsUnit a.det) (m x : Mt k r) :
    conjM a (lmulM (Matrix.of m) x) = lmulM (Matrix.of (conjM a m)) (conjM a x) := by
  apply Matrix.of.injective
  have hl : ∀ (b : Mat k r) (y : Mt k r), Matrix.of (lmulM b y) = b * Matrix.of y := fun _ _ => rfl
  rw [of_conjM, hl, hl, of_conjM, of_conjM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.one_mul]

theorem mulVec_conj_iff (a M : Mat k r) (ha : IsUnit a.det) (w w' : Fin (2 * r + k + 1) → ℂ) :
    M *ᵥ (a *ᵥ w) = a *ᵥ w' ↔ (a⁻¹ * M * a) *ᵥ w = w' := by
  constructor
  · intro h
    have h' := congrArg (fun u => a⁻¹ *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec] at h'
    rw [← h', Matrix.mul_assoc]
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a ha, Matrix.one_mul]

theorem mem_realPts_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n : ι → Mat k r)
    (hn : ∀ v, IsUnit (n v).det) (m : ι → Mt k r) :
    m ∈ realPts (fun v y => n v *ᵥ Φ v y) Γ ↔ (fun v => conjM (n v)⁻¹ (m v)) ∈ realPts Φ Γ := by
  have key : ∀ v (w w' : Fin (2 * r + k + 1) → ℂ),
      (Matrix.of (m v) *ᵥ (n v *ᵥ w) = n v *ᵥ w') ↔ Matrix.of (conjM (n v)⁻¹ (m v)) *ᵥ w = w' := by
    intro v w w'
    rw [mulVec_conj_iff _ _ (hn v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hn v)]
  simp only [realPts, Set.mem_ofPred_eq, key]

theorem mem_RP_iff (n₁ g n₂ : ι → Mat k r) (h₁ : ∀ v, n₁ v ∈ Nset k r) (h₂ : ∀ v, n₂ v ∈ Nset k r)
    (x : ι → Mt k r) :
    x ∈ RP k r g ↔ (fun v => conjM (n₂ v)⁻¹ (x v)) ∈ RP k r (fun v => n₁ v * g v * n₂ v) := by
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (h₂ v).1
  simp only [RP, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  rw [StabHaar.Rset_conj (g v) (h₁ v) (h₂ v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hu v)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu v), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (hu v)]

private theorem conjM_conjM_inv {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a (conjM a⁻¹ y) = y := by
  have h := congrFun (StabHaar.conj_conj a a⁻¹) y
  rw [Matrix.mul_nonsing_inv a ha, StabHaar.conj_one] at h
  exact h

private theorem conjM_inv_conjM' {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a⁻¹ (conjM a y) = y := by
  have h := congrFun (StabHaar.conj_conj a⁻¹ a) y
  rw [Matrix.nonsing_inv_mul a ha, StabHaar.conj_one] at h
  exact h

theorem isFund_conj_and_measure : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k r : ℕ) (ι : Type) [Fintype ι] (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n₁ g n₂ : ι → Mat k r) (Ω : Set (ι → Mt k r)) (lam : Measure (Mt k r)), SigmaFinite lam → (∀ v, n₁ v ∈ Nset k r ∧ n₂ v ∈ Nset k r ∧ IsUnit (g v).det) → IsFund (realPts Φ Γ) (RP k r (fun v => n₁ v * g v * n₂ v)) Ω → IsFund (realPts (fun v y => n₂ v *ᵥ Φ v y) Γ) (RP k r g) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) ∧ Measure.pi (fun v => lam.map (conjM (n₂ v)⁻¹)) Ω = Measure.pi (fun _ : ι => lam) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) := by
  intro K V _ _ _ k r ι _ Φ Γ n₁ g n₂ Ω lam hlam hN hF
  have := hlam
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (hN v).2.1.1
  have hui : ∀ v, IsUnit ((n₂ v)⁻¹).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hu v)
  let e : ∀ _ : ι, Mt k r ≃ᵐ Mt k r := fun v => StabHaar.conjE (n₂ v)⁻¹ (hui v)
  let E : (ι → Mt k r) ≃ᵐ (ι → Mt k r) := MeasurableEquiv.piCongrRight e
  let Cf : (ι → Mt k r) → (ι → Mt k r) := fun x v => conjM (n₂ v) (x v)
  have hEC : ∀ y, E (Cf y) = y := fun y => funext fun v => conjM_inv_conjM' (hu v) (y v)
  have hCE : ∀ y, Cf (E y) = y := fun y => funext fun v => conjM_conjM_inv (hu v) (y v)
  have hC : Cf '' Ω = E ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show E (Cf x) ∈ Ω
      rw [hEC]
      exact hx
    · intro hy
      exact ⟨E y, hy, hCE y⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show MeasurableSet (Cf '' Ω)
    rw [hC]
    exact E.measurable hF.1
  · intro x hx
    have hx' : E x ∈ RP k r (fun v => n₁ v * g v * n₂ v) :=
      (mem_RP_iff n₁ g n₂ (fun v => (hN v).1) (fun v => (hN v).2.1) x).1 hx
    obtain ⟨m', ⟨hm'Γ, hm'Ω⟩, huniq⟩ := hF.2 (E x) hx'
    have hR : ∀ m, m ∈ realPts (fun v y => n₂ v *ᵥ Φ v y) Γ ↔ E m ∈ realPts Φ Γ :=
      fun m => mem_realPts_iff Φ Γ n₂ hu m
    have hM : ∀ m, E (mulP m x) = mulP (E m) (E x) := fun m =>
      funext fun v => conjM_lmulM (hui v) (m v) (x v)
    refine ⟨Cf m', ⟨(hR _).2 (by rw [hEC]; exact hm'Γ), ?_⟩, ?_⟩
    · show mulP (Cf m') x ∈ Cf '' Ω
      rw [hC]
      show E (mulP (Cf m') x) ∈ Ω
      rw [hM, hEC]
      exact hm'Ω
    · rintro m ⟨hmΓ, hmΩ⟩
      have hmΩ' : E (mulP m x) ∈ Ω := by
        have h0 : mulP m x ∈ Cf '' Ω := hmΩ
        rw [hC] at h0
        exact h0
      have h1 : E m = m' := huniq (E m) ⟨(hR m).1 hmΓ, by rw [← hM]; exact hmΩ'⟩
      rw [← h1, hCE]
  · have hmp : MeasurePreserving E (Measure.pi fun _ : ι => lam)
        (Measure.pi fun v => lam.map (e v)) :=
      haveI : ∀ v, SigmaFinite (lam.map (e v)) := fun v => (e v).sigmaFinite_map
      measurePreserving_pi _ _ (fun v => ⟨(e v).measurable, rfl⟩)
    show _ = Measure.pi (fun _ : ι => lam) (Cf '' Ω)
    rw [hC, hmp.measure_preimage_equiv]
    rfl
end GlobalTheory.DegVol.UnipConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormStabilizerMeasureEqAnyNormalForm
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]
      exact (conj_cont n₂⁻¹).measurable.aemeasurable⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covTC_holds : CovTC := by
  intro D large₂ X Y u C hStd t N hAd μ K hμ hK
  obtain ⟨hCM, hPl, hvI, hv1, -, hcard, -, -, -, hnorm, hrk, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hTerm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hStd t N hAd
  obtain ⟨β, n₁, g, n₂, hF⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u C hStd t N hAd
  have hι : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    exact ⟨(hPl.2 w).choose⟩
  obtain ⟨τ0⟩ := id hι

  have hμeq : ∀ τ, μ τ = (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) ∧
      SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := fun τ => by
    obtain ⟨h1, h2, hinv, hFr⟩ := hF τ
    obtain ⟨-, -, -, -, ⟨c, hc⟩, -⟩ := hFr
    have hm := hμ τ
    rw [hinv] at hm
    exact GlobalTheory.Amp.StabHaar.normalFormStabilizerMeasure_eq_any_normalForm _ _ _ N.j_le _ _ _ _ _ β c _ h1 h2 hc hm
  haveI : SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := (hμeq τ0).2

  have hrat := GlobalTheory.TypeAsm.gam_iff_nLam D large₂ X Y u hStd t N hAd
  have hGiso : ∀ n ∈ (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    fun n hn => ((hrat n).1 hn).1.1.1
  have hpts : GlobalTheory.DegVol.realPts (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = trI C '' ROinf t := by
    rw [GlobalTheory.TypeAsm.RatIsomReal.realPts_eq_image D X C _ hGiso]
    congr 1
    ext y
    constructor
    · rintro ⟨x, n, hx, rfl, hn⟩
      obtain ⟨h1, h2⟩ := (hrat n).1 hn
      exact ⟨x, n, hx, rfl, h1, h2⟩
    · rintro ⟨x, n, hx, rfl, h1, h2⟩
      exact ⟨x, n, hx, rfl, (hrat n).2 ⟨h1, h2⟩⟩
  have hfund0 := GlobalTheory.CovFund.isFund_image D X Y u C t K hK
  rw [← hpts] at hfund0
  have hRP : GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹) =
      GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => n₁ τ * g τ * n₂ τ) := by
    congr 1; funext τ; exact (hF τ).2.2.1
  rw [hRP] at hfund0

  have hunit : ∀ τ, n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ IsUnit (g τ).det :=
    fun τ => ⟨(hF τ).1, (hF τ).2.1, GlobalTheory.Amp.StabHaar.unit_of_GG (hF τ).2.2.2.2.2.2.2.1.choose_spec.1⟩
  obtain ⟨hFund, hvol⟩ := GlobalTheory.DegVol.UnipConj.isFund_conj_and_measure D.host.E (VS D).V D.R.k D.R.rS D.what₂.Tau
    (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) n₁ g n₂ (trI C '' K)
    (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) inferInstance hunit hfund0
  have hF' : ∀ τ, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) β
      (fun y => n₂ τ *ᵥ phiV C τ y) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ) := fun τ => by
    rw [hvI]; exact (hF τ).2.2.2
  have hle := GlobalTheory.T.hermitian_stabiliser_covolume_le D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D) β
    (fun τ y => n₂ τ *ᵥ phiV C τ y) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) g hPl hrk hF'
    (by rw [hAd.1, hnorm, hvI, hcard]) (by rw [hvI]; exact hv1) (gS D) t.lam _ (by omega) hTerm hFund
  have hμpi : Measure.pi μ = Measure.pi fun τ => (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) := by
    congr 1; funext τ; exact (hμeq τ).1
  rw [hμpi, hvol]
  refine hle.trans (le_of_eq ?_)
  rw [hvI, hcard]
  rfl

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeightStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  first | exact @GlobalTheory.TypeAsm.covTC_holds | exact GlobalTheory.TypeAsm.covTC_holds | (intros; apply GlobalTheory.TypeAsm.covTC_holds <;> assumption)
end

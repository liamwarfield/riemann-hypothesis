module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartIndexInjectiveOffLastStep
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.TwTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}
  {A : TwDat I l Z u a Ch}

theorem cosetIn_eq_empty {j : ℕ} (h : j + 1 ≠ B.R.m) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u j) : cosetIn p = fun _ => ∅ := by
  have h1 : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) h] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h1]

theorem chartIndex_injective_offLastStep (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) (h : j + 1 ≠ B.R.m) : Function.Injective (A.b0 j) := fun α β e =>
  hA.chart_ext j hj α β e (by rw [cosetIn_eq_empty h, cosetIn_eq_empty h])

theorem subsingleton_top (hA : A.Is) : Subsingleton (Ch B.R.m) :=
  ⟨fun α β => chartIndex_injective_offLastStep hA le_rfl (by omega) (by rw [Idx.eq_top (A.b0 _ α) le_rfl, Idx.eq_top (A.b0 _ β) le_rfl])⟩


section Pin
variable {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom kom' : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd dd' : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w w' : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram Ram' : ∀ j, Set (ColT I l u a j)}
    {rd rd' : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

end Pin

end GlobalTheory.AdForm.TwTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdEmbEvz
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemGinfCOfFinM
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.EvzDecomp

theorem bc_mem_UJ' {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B) (s : A →+* A)
    (s' : B →+* B) (hs : ∀ a, φ (s a) = s' (φ a)) (J : Matrix n n A) {g : GL n A} (hg : g ∈ Formalism.UG.UJ s J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ s' (J.map φ) := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show Formalism.UG.cT s' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  have e : Formalism.UG.cT s' ((g : Matrix n n A).map φ) = (Formalism.UG.cT s (g : Matrix n n A)).map φ := by
    ext i j; simp [Formalism.UG.cT, hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem finM_one' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl]
  have e : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
    have := GlobalTheory.AdForm.RdLaw.mt_mul V 1 1
    simpa using this
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finM_pf' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    finM V hn (GlobalTheory.AdForm.RdLaw.pf V g) = finM V hn g := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.finM_pf V g

theorem infM_mul' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem mem_GinfC_of_finM {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : finM V hn k = 1) :
    k ∈ GinfC V := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl] at hk
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e] at hk
  show finHom V k = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have := congrFun (congrFun hk i) j
  simp only [Matrix.map_apply] at this
  have h3 := congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm this
  rw [AlgEquiv.symm_apply_apply] at h3
  rw [h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isBlock_one {R : Type} [Zero R] [One R] {N n : ℕ} (hN : N = n + 1) {G : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} (h : GlobalTheory.BranchFormula.IsBlock hN G A 1) (hA : A = 1) : G = 1 := by
  subst hN hA
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rw [Matrix.one_apply_eq]; exact h.2.2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']; exact (h.2.1 b).2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]; exact (h.2.1 a).1
  · have e := h.1 a b
    have e2 : G (Fin.castSucc a) (Fin.castSucc b) = (1 : Matrix (Fin n) (Fin n) R) a b := e
    rw [e2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]

theorem ratPt {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (hG : V.gram.reindex (finCongr hn) (finCongr hn) = 1) (γ₀ : GL (Fin n) D.host.E)
    (hγ : γ₀ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) 1) :
    ∃ γ ∈ GQ V, finM V hn γ = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀).1 ∧
      ∀ τ, infM θ V hn γ⁻¹ τ = atInf (Formalism.L2.Forms.embT D) ((γ₀⁻¹ : GL (Fin n) D.host.E) : Matrix _ _ _) τ := by
  subst hn
  have hG' : V.gram = 1 := by simpa using hG
  have hmem : Formalism.UG.bc (incA D) γ₀ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have := bc_mem_UJ' (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (AF D.host.F) D.sp.cm.sig) (fun x => ?_) 1 hγ
    · rw [hG']
      have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      show Formalism.UG.bc (incA D) γ₀ ∈ Formalism.UG.UJ _ ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _)
      exact this
    · show sigR (AF D.host.F) D.sp.cm.sig (1 ⊗ₜ x) = _
      simp [sigR]
      rfl
  let γ : GA D V := ⟨_, hmem⟩
  have hmt : Formalism.L2.Theta.mt V γ = (γ₀ : Matrix _ _ _).map (incA D) := rfl
  have hmt' : Formalism.L2.Theta.mt V γ⁻¹ = ((γ₀⁻¹ : GL (Fin V.rank) D.host.E) : Matrix _ _ _).map (incA D) := rfl
  refine ⟨γ, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (hG' ▸ hγ))
  · exact GlobalTheory.AdForm.RdLaw.rat_finM V γ₀ γ hmt
  · intro τ
    exact GlobalTheory.AdForm.RdLaw.rat_infM θ hθ V γ₀⁻¹ γ⁻¹ hmt' τ

theorem infM_fin'' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem ext_finM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (y : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), GlobalTheory.Core.Rk.Top.HasMat h y → IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) y.1 (finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)) := by
  intro B X I hOk hPins l Z u emb hEmb h y hM
  obtain ⟨e1, e2⟩ := hEmb h
  have hinc : (toEAf (I.rec7 l Z)).comp (incA (I.rec7 l Z)) =
      Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
    ext x
    show (Algebra.TensorProduct.comm _ _ _) (finPart (I.rec7 l Z) (1 ⊗ₜ x)) = x ⊗ₜ 1
    have : finPart (I.rec7 l Z) (1 ⊗ₜ x) = (1 : Af (I.rec7 l Z).host.F) ⊗ₜ x := by
      show Algebra.TensorProduct.map _ _ (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [this]; rfl
  have hy : y.1 = ((Formalism.L2.Theta.mt _ h).map (toEAf (I.rec7 l Z))).reindex (finCongr (rankP (I.rec7 l Z)))
      (finCongr (rankP (I.rec7 l Z))) := by
    ext i j
    have := hM.2 ((finCongr (rankP (I.rec7 l Z))).symm i) ((finCongr (rankP (I.rec7 l Z))).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have h3 := congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) e1
    simp only [Matrix.map_mul, Matrix.map_map] at h3
    rw [hy, ← hinc]
    exact h3
  · funext i
    have h3 := congrArg (toEAf (I.rec7 l Z)) (congrFun e2 i)
    rw [RingHom.map_mulVec] at h3
    rw [← hinc]
    exact h3

theorem top_lev_chi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c (g : TC.GA B (B.R.N B.R.m)), IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.y c).1.1 g.1 → ∃ κ : (A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.U, (show TC.GA B (B.R.N B.R.m) from κ.1) = (show TC.GA B (B.R.N B.R.m) from ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1)⁻¹ * (ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)⁻¹ * g ∧ (((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a Ch₀ A hA bad K hRP c g hg
  have R := hA.reads B.R.m le_rfl
  have hTop := hA.top (A.chOf B.R.m ((I.perIn u a).tilC c))
  have h1 := hTop ((I.stX a).rep c).1.1 (K.y c).1 g (hRP.pt c) hg
  have hmv := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have h2 := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1⁻¹ _ _ h1
  set g₀ := (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) with hg₀
  let κ' : (I.stp u a B.R.m).G (I.perIn u a).b0 := ((1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)), g₀.2)
  have hgam1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ' = 1 := by
    show Formalism.L2.Col.ufGL _ _ (1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)) = 1
    simp
  have hq : ((g₀.1⁻¹, 1, 1) : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m) × Formalism.L2.Col.GLG (E := B.fields.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × Formalism.L2.Col.GLQ B.fields.E (B.R.N B.R.m) (Formalism.L2.Col.QE I.sel ↑(I.tup a))) • (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) =
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    have e0 : (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) = ((I.perIn u a).tilPt c).1.1 := rfl
    rw [e0, ← hmv]
    show _ = Formalism.L2.Col.FrmG.incl _ _ κ' • _
    show _ • (Formalism.L2.Col.FrmG.incl _ _ g₀ • _) = _
    rw [smul_smul]
    congr 1
    ext1
    · simp [κ', Formalism.L2.Col.FrmG.incl]
    · ext1 <;> simp [κ', Formalism.L2.Col.FrmG.incl]
  have hr : ratAd B.host.F g₀.1⁻¹ = (ratAd B.host.F g₀.1)⁻¹ := by
    show Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1⁻¹) = (Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1))⁻¹
    rw [map_inv, map_inv]
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  have hpt : TC.PtOf (Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)))
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    rw [← hq]
    have e : Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) =
        ratAd B.host.F g₀.1⁻¹ * (g * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))) := by
      rw [hr]; group
    rw [e]
    exact h2
  have hcos := GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (u := u) (a := a) (i := B.R.m) (by omega)
    ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)))
    ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))
  have hxU := (R.lev ((I.perIn u a).tilC c) (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) _ hpt).2 ⟨κ', hgam1, rfl, hcos⟩
  refine ⟨⟨_, hxU⟩, rfl, ?_⟩
  exact R.chr ((I.perIn u a).tilC c) ⟨_, hxU⟩ κ' hgam1 hpt

end GlobalTheory.AdForm.EvzDecomp


open GlobalTheory.AdForm.EvzDecomp in
theorem GlobalTheory.AdForm.TwDat.Is.evz_decomp : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∃ γ ∈ GQ ((I.rec7 l Z).sp.X B.R.m), ∃ k ∈ GinfC ((I.rec7 l Z).sp.X B.R.m), ∃ κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)), emb h = γ * (A.h B.R.m _ ⟨(I.perIn u a).tilC c, rfl⟩ * k) * κ.1 ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ y : (I.chain l u a).Y B.R.m, ∃ y' : (I.chain l u a).Y B.R.m, IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ ∧ (A.chi B.R.m _ κ : ℂ) * φ ((I.perIn u a).tilC c) y' = (I.per l u a).evz φ c y := by
  intro B X I hOk hPins l Z u a Ch₀ A hA θ hθ emb hEmb bad K hRP c h hM
  have hExt := ext_finM_emb I hOk hPins l Z u emb hEmb h (K.y c).1 hM
  have hinvM : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, finM_one']
  have hinvM' : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, inv_mul_cancel, finM_one']
  let gU : TC.GA B (B.R.N B.R.m) := ⟨finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h),
    finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)⁻¹, hinvM _, hinvM' _⟩
  obtain ⟨κ0, hκ0, hχ0⟩ := top_lev_chi I hOk hPins l Z u a Ch₀ A hA bad K hRP c gU hExt
  have hG : ((I.rec7 l Z).sp.X B.R.m).gram.reindex (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl))
      (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl)) = 1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 B.R.m le_rfl).1
  obtain ⟨γ, hγQ, hγf, hγi⟩ := ratPt θ hθ _ (rankN (I.rec7 l Z) B.R.m le_rfl) hG
    (Formalism.L2.Col.ufGL _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
    (GlobalTheory.Mem.Col2.DnAdel.ufGL_UJ B.sp.cm _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
  obtain ⟨hh₀f, hh₀m⟩ := hA.h B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩
  set h₀ := A.h B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩ with hh₀
  set Zr := (γ * h₀)⁻¹ * emb h with hZr
  set κA := GlobalTheory.AdForm.RdLaw.pf _ Zr with hκA
  have hκAf : κA ∈ GfC _ := GlobalTheory.AdForm.RdLaw.pf_fin _ Zr
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  set Rr := ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1 with hRr
  have e1 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = gU.1 := by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, hZr, mul_inv_cancel_left]
  have e2 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) = (Rr * Y).1 := by
    rw [GlobalTheory.AdForm.StabMove.finM_mul, hγf, hh₀m]; rfl
  have e3 : (Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr) = gU.1 := by rw [← e2]; exact e1
  have hfZ : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = ((Rr * Y)⁻¹ * gU).1 := by
    have e4 : ((Rr * Y)⁻¹ * gU).1 = ((Rr * Y)⁻¹).1 * ((Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr)) := by rw [Units.val_mul, e3]
    rw [e4, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hκ0' : (show TC.GA B (B.R.N B.R.m) from κ0.1) = (Rr * Y)⁻¹ * gU := by rw [hκ0, _root_.mul_inv_rev]
  have hfκ : κ0.1.1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) κA := by
    rw [finM_pf', hfZ, ← hκ0']
  have hκU : κA ∈ A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) :=
    (hA.U B.R.m le_rfl _ κA).2 ⟨hκAf, κ0, hfκ⟩
  let κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) := ⟨κA, hκU⟩
  have hchi := hA.chi B.R.m le_rfl _ κ κ0 hfκ
  set k := Zr * κA⁻¹ with hk
  have hkC : k ∈ GinfC _ := mem_GinfC_of_finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) k (by
    rw [hk, GlobalTheory.AdForm.StabMove.finM_mul, ← finM_pf' _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr, ← hκA, hinvM])
  have hInf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) τ = 1 := fun τ =>
    isBlock_one (Formalism.L2.Col.N_m_succ B.R)
      (GlobalTheory.EmbTopBlock.isBlock_infM_emb I hOk hPins l Z u θ hθ emb (Formalism.L2.Col.N_m_succ B.R) hEmb h τ)
      (infM_fin'' θ _ (rankP (I.rec7 l Z)) h hM.1 τ)
  refine ⟨γ, hγQ, k, hkC, κ, ?_, ?_⟩
  · show emb h = γ * (h₀ * (Zr * κA⁻¹)) * κA
    rw [hZr]; group
  · intro φ _ y
    refine ⟨frMul B.fields.emb B.embLL ((I.stp u a B.R.m).gam (I.perIn u a).b0
      ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ y, ?_, ?_⟩
    · intro τ
      have ek : k = h₀⁻¹ * γ⁻¹ * (emb h * κA⁻¹) := by rw [hk, hZr]; group
      have hk' : infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k τ = ((((I.stp u a B.R.m).gam (I.perIn u a).b0
          ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ : GL (Fin (B.R.N B.R.m)) B.fields.E) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E).map (Formalism.L2.Col.embAt B.embLL B.fields.emb τ) := by
        rw [ek, infM_mul', infM_mul', infM_mul', infM_fin'' θ _ _ h₀⁻¹ (inv_mem hh₀f), hInf,
          infM_fin'' θ _ _ κA⁻¹ (inv_mem hκAf), one_mul, mul_one, mul_one, hγi τ,
          GlobalTheory.Mem.Col2.LowerTie.embT_eq I l Z]
        rfl
      rw [hk']
      rfl
    · rw [hchi, hχ0]
      rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_emb_evz : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ β, ((∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1) ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∀ y, A.rd θ B.R.m le_rfl β φ y (emb h) = (I.per l u a).evz φ c y := by
  intro B X I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK β
  refine ⟨fun hfin => GlobalTheory.AdForm.LevChiTop.emb_mem_chi I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β, ?_⟩
  intro φ hφ c h hh y
  have hβ := GlobalTheory.AdForm.TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA ((I.perIn u a).tilC c) β
  subst hβ
  obtain ⟨γ, hγ, k, hk, κ, he, hv⟩ := GlobalTheory.AdForm.TwDat.Is.evz_decomp I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK c h hh
  obtain ⟨y', hy', hval⟩ := hv φ hφ y
  rw [he, (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch₀ A hA θ hθ B.R.m le_rfl φ hφ).2 _ y γ hγ ⟨(I.perIn u a).tilC c, rfl⟩ k hk κ y' hy']
  exact hval

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem trc_single_apply {D : D7} {V : HSp D} (b : GA D V) (ε : ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc (Finsupp.single b ε) f x = ε * f (x * b) := by
  unfold trc
  by_cases hε : ε = 0
  · simp [hε]
  · rw [Finsupp.support_single_ne_zero _ hε]
    simp [GlobalTheory.MixPer.rTrans]
end GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

def ellTop (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) :
    (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ] ℂ :=
  (ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ)) •
    ((I.per l u a).period.flip (G' f) ∘ₗ eW.symm.toLinearMap ∘ₗ
      LinearMap.single ℂ (fun _ : (I.fm l u a).clsP => FrP (I.rec7 l Z) → ℂ) c ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun y : FrP (I.rec7 l Z) => (⟨y.1, y.2⟩ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1))))

theorem ellTop_apply (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) (φ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :
    ellTop R P eW ε G' c f φ = ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) *
      (I.per l u a).period (eW.symm (Pi.single c (fun y : FrP (I.rec7 l Z) => φ ⟨y.1, y.2⟩))) (G' f) := by
  simp only [ellT, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, LinearMap.flip_apply,
    LinearEquiv.coe_coe, LinearMap.coe_single, smul_eq_mul]
  rfl

@[reducible] def clsTop (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ)
    (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X')
    (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ) (G' : CXP R P t → (I.per l u a).Mt) :
    ClsT (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := (I.fm l u a).clsP
  U := UT
  h := h
  ell := fun _ _ _ c f => ellTop R P eW ε G' c f

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodLawMovedLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodLawMovedLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TopInv

theorem multT_right {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (x : (⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) →ₗ[ℂ] GA D V → ℂ) (hx : x ∈ MultT θ M J χ)
    (v : ⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) : ∀ k ∈ J, ∀ g, x v (g * k) = χ k * x v g := by
  rw [mem_multT] at hx
  intro k hk g
  have key : ∀ T ∈ Mult θ M J χ, ∀ w, T w (g * k) = χ k * T w g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hT.lev w k hk g
    | zero => intro w; simp
    | add T T' _ _ h h' => intro w; simp [h, h', mul_add]
    | smul c T _ h => intro w; simp [h]; ring
  obtain ⟨T, rfl⟩ : ∃ T, x = PiTensorProduct.lift T := ⟨_, (PiTensorProduct.lift.apply_symm_apply x).symm⟩
  rw [LinearEquiv.symm_apply_apply] at hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w => simp [key _ hx w]; ring
  | add a b ha hb => simp [ha, hb, mul_add]

theorem rd_right {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.AdForm.rd_charts I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ0 * (A.h j b c * k0) * κ0 * κ.1 = γ0 * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd γ0 hγ0 c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

end GlobalTheory.AdForm.TopInv


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.AdForm.TopInv.law_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  intro B X I hOk hP l Z u G _ _ Pl0 Tt F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hT bad K eW hRd heW hbT hLev htl n hn ψ hψ f v y β x κ hκ
  subst hn
  unfold PinChL at hCh
  have hm : (I.rec7 l Z).R.m ≤ B.R.m := le_rfl
  rw [hT.eT, trc_single_apply, trc_single_apply]
  have hκ' := (hT.lev κ).1 hκ
  obtain ⟨κ', hκ'm⟩ := (hLev.1 κ).1 hκ'
  have hchi := hLev.2 κ κ' hκ'm
  have hx := f.2
  dsimp only [CXP] at hx
  have hr := multT_right _ _ _ _ _ hx v
  have hf := hr _ hκ' (x * g.bT)
  have e : x * g.bT * (g.bT⁻¹ * κ * g.bT) = x * κ * g.bT := by group
  rw [e] at hf
  obtain ⟨hU, hchiU, hnorm⟩ := (GlobalTheory.AdForm.rd_emb_evz I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hT.emb bad K hRd (ι _ β)).1 (GlobalTheory.AdForm.LevChiTop.chi_pow_of_levG K hLev) κ κ' hκ'm
  have hψF : ψ ∈ (I.fm l u a).Fi _ := ((hCh.ram _ hm ψ).1 hψ).1.1
  have hemb : (g.oT _ rfl).emb (x * κ, 1) = (g.oT _ rfl).emb (x, 1) * ((g.oT _ rfl).emb.comp (MonoidHom.inl _ _)) κ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hq : ∀ z, k.rd (I.rec7 l Z).R.m β ψ y z = A.rd R.θ _ hm (ι _ β) ψ y z := fun z => congrFun (hCh.rdq _ hm β ψ y) z
  have hr2 : A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1) * ((g.oT (I.rec7 l Z).R.m rfl).emb.comp (MonoidHom.inl _ _)) κ) = ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1)) :=
    rd_right I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hm ψ hψF _ y _ ⟨_, hU⟩
  have hc : ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) = ((K.lev.chi κ' : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hchiU
  rw [hemb, hq, hq, hr2, hc, hf, hchi]
  have h1 : star ((K.lev.chi κ' : ℂˣ) : ℂ) * ((K.lev.chi κ' : ℂˣ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]; simp
  linear_combination (ε * f.1 v (x * g.bT) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1))) * h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodLawMovedLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriod_law_movedLevel : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  first | exact @GlobalTheory.AdForm.TopInv.law_top | exact GlobalTheory.AdForm.TopInv.law_top | (intros; apply GlobalTheory.AdForm.TopInv.law_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodTailEqLoweredEvaluationPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamTEqLamTHcW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvzVal

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_eq_lamT_hcW {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem evz_mem_valC : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (ψ : ColT I l u a B.R.m), ψ ∈ (I.fm l u a).Fi B.R.m → ∀ c, (fun y : FrN (I.rec7 l Z) (B.R.N B.R.m) => (I.per l u a).evz ψ c ⟨y.1, y.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m) := by
  intro B X I hI hP l Z u a ψ hψ c
  have h1 := (hψ ((I.perIn u a).tilC c)).1
  have h2 := GlobalTheory.Mem.Col2.Law.tr_mem (I.stp u a B.R.m) B.fields.emb B.embLL _ (I.perIn u a).b0
    ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) h1
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 h2
  rw [lamT_eq_lamT_hcW I l Z u B.R.m]
  exact ⟨P, hP, funext fun y => congrFun e ⟨y.1, y.2⟩⟩

end GlobalTheory.EvzVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodTailEqLoweredEvaluationPeriod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm


open _root_.Formalism.L2.Col in
theorem tailTop_eq_of_pin : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hRP heW hbT hLev hG h hh hst G' hG' n hn ψ hψ f
  subst hn
  have hC : PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK := hCh
  have hIs : A.Is := hC.is
  have hψF : ψ ∈ (I.fm l u a).Fi B.R.m := ((hC.ram B.R.m le_rfl ψ).1 hψ).1.1
  have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := N_m_succ B.R

  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = (I.per l u a).lowerMap ((I.per l u a).evz ψ) := ⟨_, rfl⟩
  have hlow : ∀ c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)),
      Lz c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) y :=
    fun c y => hLz ▸ (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.2.2 a _ c y
  have heL : ∀ c, eW Lz c = fun y => lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) ⟨y.1, y.2⟩ := by
    intro c; funext y
    rw [heW Lz c y ⟨y.1, y.2⟩ rfl]
    exact hlow c ⟨y.1, y.2⟩

  have hw : ∀ c, eW Lz c ∈ LinearMap.range j := by
    intro c
    rw [hj.range]
    have hv0 := GlobalTheory.EvzVal.evz_mem_valC I hI hP l Z u a ψ hψF c
    have hv1 := (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.1.1 _ hv0
    obtain ⟨Pp, hPp, hEq⟩ := hv1
    rw [heL c]
    exact ⟨Pp, hPp, funext fun y => congrFun hEq ⟨y.1, y.2⟩⟩
  obtain ⟨G'', hR'', htl⟩ := hG ψ f
  have hper : (I.per l u a).Ptil ψ (G' f) = tl ψ f := by
    rw [htl]
    have := GlobalTheory.Fam.Check.ReadsG.period_eq K eW j g.bT (hG' f) hR'' Lz hw
    rw [hLz] at this
    exact this

  have hsum : ∀ β : k.Ch B.R.m, ∑ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
      (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) = ε * tl ψ f := by
    intro β
    have hev : ∀ c y, A.rd R.θ B.R.m le_rfl (ι B.R.m β) ψ y ((g.oT B.R.m rfl).emb (h c, 1)) = (I.per l u a).evz ψ c y :=
      fun c y => (GlobalTheory.AdForm.rd_emb_evz I hI hP l Z u a Ch₀ A hIs R.θ hX.inf _ hTop.emb bad K hRP (ι B.R.m β)).2 ψ hψF c (h c) (hh c) y
    have hterm : ∀ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
        (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) =
        ε * (I.per l u a).period (eW.symm (Pi.single c (eW Lz c))) (G' f) := by
      intro c
      have hne : (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := (I.fm l u a).stabilizer₂ c)).ne'
      have e2 : (fun z : FrN (I.rec7 l Z) (B.R.N B.R.m) => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1))) =
          fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩ := by
        funext z
        exact (congrFun (hC.rdq B.R.m le_rfl β ψ _) _).trans (hev c _)
      rw [e2, ellTop_apply, hst c, heL c]
      field_simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum]
    have e3 : ∑ c, Pi.single c (eW Lz c) = eW Lz := Finset.univ_sum_single _
    rw [e3, LinearEquiv.symm_apply_apply, ← hper, hLz]
    rfl
  have hsub : Subsingleton (k.Ch B.R.m) :=
    ⟨fun β β' => hC.live.inj B.R.m ((GlobalTheory.AdForm.TwTest.subsingleton_top hIs).elim _ _)⟩
  rw [hTop.cP]
  have htail : ∀ hm, (tupOf R P u g t r k tl).tail _ hm ψ f = tl ψ f := fun _ => rfl
  rw [htail]
  refine (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (Finset.sum_congr rfl fun β _ => hsum β)).trans ?_
  have e1 : ∀ {α : Type} (inst : Fintype α), (∀ a b : α, a = b) → α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = x := by
    intro α inst hs a x
    haveI : Unique α := ⟨⟨a⟩, fun b => hs _ _⟩
    exact Fintype.sum_unique _
  have e0 : ∀ {α : Type} (inst : Fintype α), IsEmpty α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = 0 := by
    intro α inst hE x
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rcases isEmpty_or_nonempty (k.Ch B.R.m) with hE | hne
  · have h0 : ψ = 0 := by
      funext c
      obtain ⟨β, -⟩ := hC.live.last (A.chOf B.R.m c)
      exact (hE.false β).elim
    have h1 : tl ψ f = 0 := by
      rw [← hper, h0]
      show ((I.per l u a).period ((I.per l u a).lowerMap ((I.per l u a).evz 0))) (G' f) = 0
      simp only [map_zero, LinearMap.zero_apply]
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e0 _ hE _)).trans (by rw [h1]; ring)
  · obtain ⟨β₀⟩ := hne
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e1 _ (fun a b => hsub.elim a b) β₀ _)).trans (by ring)

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodTailEqLoweredEvaluationPeriodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  first | exact @GlobalTheory.AdForm.tailTop_eq_of_pin | exact GlobalTheory.AdForm.tailTop_eq_of_pin | (intros; apply GlobalTheory.AdForm.tailTop_eq_of_pin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSpaceMovedLevelClassPointsRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSpaceMovedLevelClassPointsRepresentatives
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ClassPtReps
variable {D : D7}

theorem hasMat_iff (h : GA D D.sp.X') (y) :
    GlobalTheory.Core.Rk.Top.HasMat h y ↔ h ∈ GfC D.sp.X' ∧ finM D.sp.X' (Formalism.L2.Forms.rankP D) h = y.1 := by
  have key : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j =
      finM D.sp.X' (Formalism.L2.Forms.rankP D) h (finCongr (Formalism.L2.Forms.rankP D) i) (finCongr (Formalism.L2.Forms.rankP D) j) := by
    intro i j
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Matrix.ext fun i j => ?_⟩
    have := h2 ((finCongr (Formalism.L2.Forms.rankP D)).symm i) ((finCongr (Formalism.L2.Forms.rankP D)).symm j)
    rw [key] at this
    simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j => by rw [key, h2]⟩

theorem nontrivial_finAdeles : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial

theorem inclE_inj : Function.Injective
    (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI := nontrivial_finAdeles (D := D)
  exact Formalism.UG.P.inclE_injective D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem bc_inclE_inj {n : ℕ} : Function.Injective
    (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
      GL (Fin n) D.host.E → GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => inclE_inj (D := D) ?_)
  have h2 := congrArg (fun g : GL (Fin n) _ => g.val i j) hab
  simpa [Formalism.UG.bc] using h2

theorem eq_one_of_GQ {V : HSp D} {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V rfl γ = 1) : γ = 1 := by
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  have h2 : finM V rfl γ = δ.1.map (Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl, Matrix.map_map]
    rfl
  have hδ1 : δ.1 = 1 := by
    apply Matrix.map_injective (inclE_inj (D := D))
    beta_reduce
    rw [← h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  apply Subtype.ext
  apply Units.ext
  show mt V γ = 1
  rw [e', hδ1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_GQ' {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ : GA D V} (hγ : γ ∈ GQ V) (h1 : finM V hn γ = 1) : γ = 1 := by
  subst hn
  exact eq_one_of_GQ hγ h1

theorem finGLHom_injOn {V : HSp D} {n : ℕ} (hn : V.rank = n) {γ₁ γ₂ : GA D V} (h1 : γ₁ ∈ GQ V) (h2 : γ₂ ∈ GQ V)
    (e : GlobalTheory.ClassSumLevel.finGLHom V hn γ₁ = GlobalTheory.ClassSumLevel.finGLHom V hn γ₂) : γ₁ = γ₂ := by
  have h3 : γ₁⁻¹ * γ₂ ∈ GQ V := mul_mem (inv_mem h1) h2
  have h4 : finM V hn (γ₁⁻¹ * γ₂) = 1 := by
    have := congrArg Units.val (show GlobalTheory.ClassSumLevel.finGLHom V hn (γ₁⁻¹ * γ₂) = 1 by rw [map_mul, map_inv, e, inv_mul_cancel])
    exact this
  have := eq_one_of_GQ' hn h3 h4
  rw [← mul_inv_cancel_left γ₁ γ₂, this, mul_one]

theorem card_eq_of_lift {G A : Type} [Group G] (H : Subgroup G) (p : G → Prop) (q : A → Prop) (ρ : A → G) (hρ : ∀ a, ρ a ∈ H)
    (hpq : ∀ a, p (ρ a) ↔ q a) (hi : ∀ a b, ρ a = ρ b → a = b) (hs : ∀ γ ∈ H, ∃ a, ρ a = γ) :
    Nat.card {γ : H // p γ.1} = Nat.card {a // q a} := by
  refine (Nat.card_eq_of_bijective (fun a : {a // q a} => (⟨⟨ρ a.1, hρ a.1⟩, (hpq _).2 a.2⟩ : {γ : H // p γ.1}))
    ⟨fun a b hab => Subtype.ext (hi _ _ (congrArg (fun x : {γ : H // p γ.1} => x.1.1) hab)), fun γ => ?_⟩).symm
  obtain ⟨a, ha⟩ := hs γ.1.1 γ.1.2
  exact ⟨⟨a, (hpq a).1 (ha ▸ γ.2)⟩, Subtype.ext (Subtype.ext ha)⟩


open scoped ComplexOrder in
set_option maxHeartbeats 2000000 in
theorem isReps_of_level (V : HSp D) {n : ℕ} (hn : V.rank = n) (hV : ∀ τ, (gramAt D V τ).PosDef) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → Formalism.UG.UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (h : cl → GA D V) (hf : ∀ c, h c ∈ GfC V)
    (hh : ∀ c, finM V hn (h c) = (yc c).1.1) (U : Subgroup (GA D V))
    (mem : ∀ x, x ∈ U ↔ x ∈ GfC V ∧ x ∈ GlobalTheory.ClassSumLevel.levG V hn S) :
    IsReps V U h ∧ ∀ c, stabOrd U (h c) = Nat.card {δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)) //
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 ∈
        S.U.map (MulAut.conj (yc c).1).toMonoidHom} := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.1
  haveI := hT.2.2.2.2.1
  have hinf : ∀ k ∈ GinfC V, k ∈ GlobalTheory.ClassSumLevel.levG V hn S := fun k hk =>
    ⟨1, (GlobalTheory.ClassSumLevel.finM_eq_one_of_mem_GinfC V hn hk).symm⟩
  have split : ∀ k ∈ GlobalTheory.ClassSumLevel.levG V hn S, ∃ a ∈ GinfC V, ∃ κ ∈ U, k = a * κ := by
    intro k hk
    obtain ⟨a, ha, κ, hκ, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
    refine ⟨a, ha, κ, (mem κ).2 ⟨hκ, ?_⟩, rfl⟩
    have := mul_mem (inv_mem (hinf a ha)) hk
    rwa [inv_mul_cancel_left] at this
  have hex := GlobalTheory.ClassSumLevel.existsUnique_class V hn S yc hy h hh
  refine ⟨⟨fun x hx => ((mem x).1 hx).1, ?_, ?_, hf, fun g => ?_, fun c c' γ hγ k hk κ hκ e => ?_⟩, fun c => ?_⟩
  · have hc := GlobalTheory.ClassSumLevel.isCompact_levG V hn S hV
    have hcl : IsClosed (GfC V : Set (GA D V)) := by
      have e : (GfC V : Set (GA D V)) = {g | ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g} := by
        ext g
        exact ⟨fun hg => congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (V := V) ⟨g, hg⟩), fun hg => by
          have hg' : ((GlobalTheory.AutMult.toFin V g : GfC V) : GA D V) = g := hg
          rw [← hg']
          exact (GlobalTheory.AutMult.toFin V g).2⟩
      rw [e]
      exact isClosed_eq (continuous_subtype_val.comp (GlobalTheory.AutMult.continuous_toFin V)) continuous_id
    have e : (U : Set (GA D V)) = (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) ∩ (GfC V : Set (GA D V)) :=
      Set.ext fun x => (mem x).trans and_comm
    rw [e]
    exact hc.inter_right hcl
  · have e : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' (GlobalTheory.ClassSumLevel.levG V hn S : Set (GA D V)) :=
      Set.ext fun x => ⟨fun hx => ((mem x.1).1 (Subgroup.mem_subgroupOf.1 hx)).2,
        fun hx => Subgroup.mem_subgroupOf.2 ((mem x.1).2 ⟨x.2, hx⟩)⟩
    rw [e]
    exact (GlobalTheory.ClassSumLevel.isOpen_levG V hn S).preimage continuous_subtype_val
  · obtain ⟨c, ⟨γ, hγ, k, hk, e⟩, -⟩ := hex g
    obtain ⟨a, ha, κ, hκ, rfl⟩ := split k hk
    exact ⟨γ, hγ, c, a, ha, κ, hκ, by rw [e]; simp only [mul_assoc]⟩
  · obtain ⟨c₀, -, hu⟩ := hex (h c')
    have h1 := hu c ⟨γ, hγ, k * κ, mul_mem (hinf k hk) ((mem κ).1 hκ).2, by rw [e]; simp only [mul_assoc]⟩
    have h2 := hu c' ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩
    exact h1.trans h2.symm
  · have hh' : GlobalTheory.ClassSumLevel.finGLHom V hn (h c) = (yc c).1 := Units.ext (hh c)
    have key : ∀ γ : GA D V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔
        GlobalTheory.ClassSumLevel.finGLHom V hn γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom := by
      intro γ
      have e1 : (∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) ↔ (h c)⁻¹ * γ * h c ∈ GlobalTheory.ClassSumLevel.levG V hn S := by
        constructor
        · rintro ⟨k, hk, κ, hκ, e⟩
          rw [mul_assoc, e, mul_assoc, inv_mul_cancel_left]
          exact mul_mem (hinf k hk) ((mem κ).1 hκ).2
        · intro hz
          obtain ⟨a, ha, κ, hκ, e⟩ := split _ hz
          exact ⟨a, ha, κ, hκ, by rw [mul_assoc, ← e, mul_assoc, mul_inv_cancel_left]⟩
      rw [e1, GlobalTheory.ClassSumLevel.mem_levG_iff, map_mul, map_mul, map_inv, hh']
      constructor
      · intro hz
        refine ⟨_, hz, ?_⟩
        show (yc c).1 * _ * (yc c).1⁻¹ = _
        group
      · rintro ⟨κ, hκ, e⟩
        have e' : (yc c).1 * κ * (yc c).1⁻¹ = GlobalTheory.ClassSumLevel.finGLHom V hn γ := e
        rw [← e', show (yc c).1⁻¹ * ((yc c).1 * κ * (yc c).1⁻¹) * (yc c).1 = κ by group]
        exact hκ
    have hr : ∀ δ : Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)), ∃ γ ∈ GQ V,
        GlobalTheory.ClassSumLevel.finGLHom V hn γ =
          Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 := fun δ =>
      GlobalTheory.ClassSumLevel.exists_GQ_of_mem_ratPts V hn ⟨δ.1, δ.2, rfl⟩
    choose ρ hρ eρ using hr
    unfold stabOrd
    refine card_eq_of_lift (GQ V) (fun γ => ∃ k ∈ GinfC V, ∃ κ ∈ U, γ * h c = h c * k * κ) _ ρ hρ (fun δ => (key _).trans (by rw [eρ])) (fun a b e => ?_) fun γ hγ => ?_
    · exact Subtype.ext (bc_inclE_inj (D := D) ((eρ a).symm.trans ((congrArg _ e).trans (eρ b))))
    · obtain ⟨δ, hδ, e⟩ := GlobalTheory.ClassSumLevel.finGLHom_mem_ratPts V hn hγ
      exact ⟨⟨δ, hδ⟩, finGLHom_injOn hn (hρ ⟨δ, hδ⟩) hγ ((eρ ⟨δ, hδ⟩).trans e)⟩


set_option maxHeartbeats 1000000 in
theorem isReps_stabOrd_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J _ j _ _ P t r a k tl Ch₀ A ι w _ UT ε hpin bad K eW _ _ _ hLev _ h hh
  have mem : ∀ x, x ∈ UT ↔ x ∈ GfC (I.rec7 l Z).sp.X' ∧
      x ∈ GlobalTheory.ClassSumLevel.levG (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z)) K.lev := by
    intro x
    refine ((hpin.lev x).trans (hLev.1 x)).trans ⟨?_, ?_⟩
    · rintro ⟨κ, hκ⟩
      exact ⟨hκ.1, κ, ((hasMat_iff x _).1 hκ).2.symm⟩
    · rintro ⟨h1, κ, hκ⟩
      exact ⟨κ, (hasMat_iff x _).2 ⟨h1, hκ.symm⟩⟩
  have H := isReps_of_level (I.rec7 l Z).sp.X' (Formalism.L2.Forms.rankP (I.rec7 l Z))
    (GlobalTheory.RepsObj.gramAt_posDef (D7.X'_posDef _) (I.rec7 l Z).sp.X'_sig) K.lev K.y K.y_bij h (fun c => (hh c).1)
    (fun c => ((hasMat_iff _ _).1 (hh c)).2) UT mem
  refine ⟨H.1, fun c => (H.2 c).trans ?_⟩
  exact (Nat.card_congr ((MonoidHom.ofInjective (K.stabI_inj c)).toEquiv.trans
    (Equiv.subtypeEquivRight (K.stabI_range c)))).symm

end GlobalTheory.ClassPtReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSpaceMovedLevelClassPointsRepresentativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_space_moved_level_class_points_representatives : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  first | exact @GlobalTheory.ClassPtReps.isReps_stabOrd_top | exact GlobalTheory.ClassPtReps.isReps_stabOrd_top | (intros; apply GlobalTheory.ClassPtReps.isReps_stabOrd_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_translate_real_point_read_by_period : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  first | exact @GlobalTheory.AdForm.TopTranslate.top_translate | exact GlobalTheory.AdForm.TopTranslate.top_translate | (intros; apply GlobalTheory.AdForm.TopTranslate.top_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem exists_clsT_of_pinTop : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  intro B X I hI hPins l Z u G iG iGf Pl0 T F Ks iK iNK iA R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  choose h hh using fun c : (I.fm l u a).clsP => GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
  choose G' hG' using hG 0
  obtain ⟨hrep, hst⟩ := GlobalTheory.T.last_space_moved_level_class_points_representatives I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh
  refine ⟨clsTop R g P r k tl s J UT h eW ε G', hrep, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.lastPeriod_law_movedLevel I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG
  · intro n hn f v β c x hx
    show trc (k.eT n hn β) (f.1 v) (h c * x) = ellTop R P eW ε G' c f (J v x)
    rw [hTop.eT n hn β, trc_single_apply, ellTop_apply, GlobalTheory.T.form_translate_real_point_read_by_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh G' (fun f => (hG' f).1) f v c x hx]
    ring
  · exact GlobalTheory.T.lastPeriod_tail_eq_lowered_evaluation_period I hI hPins l Z u R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hR hE hbT hLev hG h hh hst G' (fun f => (hG' f).1)

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lastPeriod_classData_of_lastStep : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∃ E : ClsT (realOf u R g s J) (tupOf R P u g t r k tl), E.Is := by
  first | exact @GlobalTheory.AdForm.exists_clsT_of_pinTop | exact GlobalTheory.AdForm.exists_clsT_of_pinTop | (intros; apply GlobalTheory.AdForm.exists_clsT_of_pinTop <;> assumption)
end

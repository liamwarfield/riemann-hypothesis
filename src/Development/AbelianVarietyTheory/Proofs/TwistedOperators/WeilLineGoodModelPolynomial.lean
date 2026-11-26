module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory Filter Topology
open scoped SchwartzMap Classical Matrix

noncomputable section

namespace GlobalTheory.ArchLinePair

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ)
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ := by
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) κ
  have hΦ₀ : tens (evI F) (⇑f) r₀ ∈ schA F κ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch _ (hpres _ hΦ₀)
  refine ⟨f₁, fun r hr => funext fun y => ?_⟩
  set u : AF F := (0, 1) with hu_def
  have hu : evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have hmul : ∀ a : AF F, u * a = (0, a.2) := fun a => Prod.ext (zero_mul _) (one_mul _)
  set ya : κ → AF F := fun i => ((y i).1, 0) with hya
  have hy : ∀ i, y i = ya i + u * y i := fun i => by
    rw [hmul]
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hτx : ∀ (Φ : (κ → AF F) → ℂ) x, schr ψ (u • y, u • (0 : κ → AF F)) Φ x = Φ (x + u • y) := fun Φ x => by
    simp only [schr, smul_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have step1 : T (tens (evI F) ⇑f r) y = T (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r)) ya := by
    have e : ya + u • y = y := funext fun i => (hy i).symm
    rw [hcomm u hu y 0 _ hr.2, hτx, e]
  have hmemτ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) ∈ schA F κ := by
    have e : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) = fun x => tens (evI F) ⇑f r (x + u • y) :=
      funext fun x => hτx _ x
    rw [e]
    exact GlobalTheory.SchwartzTranslate.schA_translate F (u • y) hr.2
  have hΨ : schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀ ∈ schA F κ :=
    Submodule.sub_mem _ hmemτ (Submodule.smul_mem _ _ hΦ₀)
  have hvan : ∀ z, At (evI F) z →
      (schr ψ (u • y, u • (0 : κ → AF F)) (tens (evI F) ⇑f r) - r y • tens (evI F) ⇑f r₀) (ya + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := GlobalTheory.ArchLocality.snd_eq_zero_of_at hz
    have e1 : ya + z + u • y = y + z := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      conv_rhs => rw [hy i]
      abel
    have e2 : (fun i => evI F ((ya + z) i)) = fun i => evI F ((y + z) i) := rfl
    have e3 : r₀ (ya + z) = 1 := hr₀1 _ fun i => by
      show (0 : FiniteAdeleRing (𝓞 F) F) + (z i).2 = 0
      rw [hz2 i, add_zero]
    rw [Pi.sub_apply, Pi.smul_apply, hτx, e1]
    simp only [tens]
    rw [hr.1 y z hz, e2, e3, smul_eq_mul]
    ring
  have hfib := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm _ hΨ ya hvan
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hfib
  have hya' : ya = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) := by
    funext i
    simp only [hya, evI, RingEquiv.symm_apply_apply]
  have hf₁' := hf₁ (fun i => evI F (y i))
  rw [step1, hfib, hya', hf₁']
  simp only [tens]
  ring

private theorem hTens_eq_trace_twisted_operators {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem map_mul_lemma_2 {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β γ : Type}
    [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem hTens_actAB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB)
    (x y : Matrix α β E) : hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  obtain ⟨⟨G, hG⟩, ⟨H, hH⟩⟩ := p
  have hG' : (G : Matrix α α E)ᵀ * JA * (G : Matrix α α E).map c = JA := hG
  have hH' : (H : Matrix β β E)ᵀ * JB * (H : Matrix β β E).map c = JB := hH
  have hG2 : ∀ N : Matrix α β E, (G : Matrix α α E)ᵀ * (JA * ((G : Matrix α α E).map c * N)) = JA * N :=
    fun N => by simpa only [Matrix.mul_assoc] using congrArg (· * N) hG'
  have hH2 : ((H : Matrix β β E).map c)ᵀ * (JBᵀ * (H : Matrix β β E)) = JBᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose hH'
  simp only [actAB, hTens_eq_trace_twisted_operators, map_mul_lemma_2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hG2, hH2]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_smul (p : UA σ X.J × UA σ W.J) (u : AF F) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (u • w) = u • actAB (cA σ) p w := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_add (p : UA σ X.J × UA σ W.J) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) p (w + w') = actAB (cA σ) p w + actAB (cA σ) p w' := by
  simp only [actAB, Matrix.mul_add, Matrix.add_mul]

theorem actAB_mul (p q : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) (p * q) w = actAB (cA σ) p (actAB (cA σ) q w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actAB_one (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) (1 : UA σ X.J × UA σ W.J) w = w := by
  simp only [actAB, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem actAB_fin {p : UA σ X.J × UA σ W.J} (h1 : p.1 ∈ UAt σ X (evI F)) (h2 : p.2 ∈ UAt σ W (evI F)) (u : AF F)
    (hu : evI F u = 0) (w : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (u • w) = u • w := by
  have e1 : u • mat p.1 = u • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    have h := h1 u hu
    rwa [smul_sub, sub_eq_zero] at h
  have e2 : u • mat p.2 = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    have h := h2 u hu
    rwa [smul_sub, sub_eq_zero] at h
  simp only [mat] at e1 e2
  simp only [actAB]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul,
    ← Matrix.transpose_smul, e2, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]

def amap (M : Model σ X W) (p : UA σ X.J × UA σ W.J) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (actAB (cA σ) p (GlobalTheory.ArchFam.wv M v))
  map_add' v v' := by
    simp only [GlobalTheory.ArchFam.wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), actAB_add,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [GlobalTheory.ArchFam.wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, actAB_smul,
      Coord.coordI_smul, RingHom.id_apply]

theorem amap_coordI (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    amap M p (Coord.coordI M w) = Coord.coordI M (actAB (cA σ) p w) := by
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.ArchFam.wv]
  rw [Coord.lift_coordI, actAB_smul, Coord.coordI_one]

theorem continuous_amap (M : Model σ X W) (v) : Continuous fun p : UA σ X.J × UA σ W.J => amap M p v := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (inferInstance : IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hev : Continuous (evI F) := by
    show Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        ((continuous_apply _).comp continuous_fst)
  have hloc : Continuous fun x : Fin n × Fin d → AF F => locV x :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have he : Continuous fun u : Matrix (Fin n) (Fin d) (AE F E) => M.co.e u :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hg : Continuous fun p : UA σ X.J × UA σ W.J => ((p.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  have hh : Continuous fun p : UA σ X.J × UA σ W.J => ((p.2 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hact : Continuous fun p : UA σ X.J × UA σ W.J => actAB (cA σ) p (GlobalTheory.ArchFam.wv M v) :=
    (hg.matrix_mul continuous_const).matrix_mul hh.matrix_transpose
  simp only [amap, LinearMap.coe_mk, AddHom.coe_mk, Coord.coordI]
  exact (hloc.comp (continuous_fst.comp (he.comp hact))).prodMk (hloc.comp (continuous_snd.comp (he.comp hact)))

end GlobalTheory.ArchLinePair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DerPol

end GlobalTheory.DerPol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMellin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFun

theorem conjugateUnitaryAdelicIso_map_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem algebraicDatum_eq_sum_pureTensors_vacua {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

end GlobalTheory.SquareAgree.LineDerFun


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeAdm

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def smAut (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f}
  add_mem' := fun ha hb => GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb
  zero_mem' := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V
  smul_mem' := fun c _ ha => GlobalTheory.Mem.AutSpace.isAutFunSm_smul c ha

theorem isAutFunSm_of_mem_gkGen (hθ : IsInfFam θ) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, IsAutFunSm θ V f := by
  have hA : GlobalTheory.CuspGK.IsGKSub θ M (smAut θ V) :=
    ⟨fun τ g hg f hf => GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf τ g hg.1,
      fun τ X hX f hf => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf⟩
  exact fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := smAut θ V) hψ hA hf

theorem level_gkGen {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g := by
  obtain ⟨U, hU, hψU⟩ := hψ.level
  let A : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g}
      add_mem' := fun ha hb u hu hu' g => by simp only [Pi.add_apply, ha u hu hu' g, hb u hu hu' g]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c f hf u hu hu' g => by simp only [Pi.smul_apply, hf u hu hu' g] }
  have hA : GlobalTheory.CuspGK.IsGKSub θ M A := by
    refine ⟨fun τ g _ f hf u hu hu' x => ?_, fun τ X _ f hf u hu hu' x => ?_⟩
    · show f (x * u * atTau θ V τ g) = f (x * atTau θ V τ g)
      rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) hu',
        ← mul_assoc]
      exact hf u hu hu' _
    · have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hu' τ X f) x
      rw [show rTr V u f = f from funext (hf u hu hu')] at this
      exact this.symm
  exact ⟨U, hU, fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := A) (fun u hu hu' g => hψU u hu hu' g) hA hf⟩

theorem gelf_mem_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (τ : D.what₂.Tau) (k : ℕ) :
    ∀ f ∈ A, gelf θ V τ k f ∈ A := by
  intro f hf
  have hC : ∀ Z, ∀ g ∈ A, RderC θ V τ Z g ∈ A := fun Z g hg => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact A.add_mem (hA.lie τ _ h1 g hg) (A.smul_mem _ (hA.lie τ _ h2 g hg))
  have key : ∀ l : List ((GA D V → ℂ) → (GA D V → ℂ)), (∀ F ∈ l, ∀ g ∈ A, F g ∈ A) →
      l.foldr (fun F acc => F acc) f ∈ A := by
    intro l hl
    induction l with
    | nil => exact hf
    | cons F l ih => exact hl F (by simp) _ (ih fun F' hF' => hl F' (by simp [hF']))
  refine Submodule.sum_mem _ fun idx _ => key _ fun F hF => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hF
  exact hC _

end GlobalTheory.KTypeAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPai
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPai
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweRealSmall

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

private theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  simp only [e, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem howe_real_ker' : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  have hR := hM.real
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  obtain ⟨hbdd, hsum⟩ := hHD F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  set K : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))) := LinearMap.ker R.p' ⊓ G.M'.Pol Bs.ψ Bs.emb with hKdef
  have hK : GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hact
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hR.quot'.lie γ hγ f hf f₁ hact), hN.1 (hN.2.1 γ hγ f hf f₁ hact)⟩
    · intro k hk f hf f₁ hact
      refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hN.1 (hN.2.2.1 k hk f hf f₁ hact)⟩
      rw [map_sub, hR.quot'.cpt k hk f hf f₁ hact, sub_self]
    · intro γ hγ f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.lie γ hγ 0 (zero_mem _) f hf'.2 0 f₁
        (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hLie γ hγ f hf'.2).2 f₁ hact⟩
    · intro k hk f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.cpt k hk 0 (zero_mem _) f hf'.2 0 f₁ (acts_zero _) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hCpt k hk f hf'.2).2 f₁ hact⟩
  have hKne : K ≠ G.M'.Pol Bs.ψ Bs.emb := by
    intro hKe
    have hbot : (G.M'.Pol Bs.ψ Bs.emb).map R.p' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← hKe] at hf
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1
    rw [hR.quot'.onto] at hbot
    haveI := hR.nontriv
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ G.M'.Pol Bs.ψ Bs.emb := hsum N K hN hK hNe hKne
  rcases hR.irred (N.map R.p') (by
    intro γ hγ f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hLie γ hγ n (hN.1 hn)).1
    rw [hR.lie γ hγ f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ n hn n₁ hactn)) (by
    intro k hk f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hCpt k hk n (hN.1 hn)).1
    rw [hR.cpt k hk f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.2 k hk n hn n₁ hactn)) with h0 | htop
  · have hmem : R.p' φ ∈ N.map R.p' := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.1 inf_le_right) ?_
    intro f hf
    have hm : R.p' f ∈ N.map R.p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : f - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hf (hN.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweRealSmall

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  first | exact @GlobalTheory.HoweRealSmall.howe_real_ker' | exact GlobalTheory.HoweRealSmall.howe_real_ker' | (intros; apply GlobalTheory.HoweRealSmall.howe_real_ker' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.HoweRealKer

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem det_ne_zero_of_sig {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]

theorem det_ne_zero_of_sigI {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (Complex.I • J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} {n m : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    ActsD (evI F) (fun t => T t) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _ x
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero, Pi.zero_apply]
  exact hasDerivAt_const 0 0

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]

theorem main : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hMt
  obtain ⟨ht, hr, -⟩ := hMt
  have w0 : InfinitePlace F := Classical.arbitrary _
  have hVdet : G.V.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV.sig w0)
  have hV'det : G.V'.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV'.sig w0)
  have hWdet : G.W.J.det ≠ 0 := det_ne_zero_of_sigI _ _ (ht.geo.hW.sig w0)
  have hresW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.β / Xc.α) (a + a') :=
    resEtaPow_div ht.chars.resβ ht.chars.resα
  have hresW' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a' + a) :=
    resEtaPow_div ht.chars.resα ht.chars.resβ
  rw [Nat.add_comm a' a] at hresW'
  have hHk := isHecke_div ht.chars.heckeβ ht.chars.heckeα
  have hHk' := isHecke_div ht.chars.heckeα ht.chars.heckeβ
  obtain ⟨hchain, hsum⟩ := hHD F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L' := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  have C := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have C' := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  refine ⟨hchain, ?_⟩
  intro N hN hNP

  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  let K : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := LinearMap.ker R.p ⊓ P
  have hK : GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ g hg g₁ hg₁
      exact ⟨LinearMap.mem_ker.mpr (hr.quot.lie γ hγ g hg g₁ hg₁), hN.1 (hN.2.1 γ hγ g hg g₁ hg₁)⟩
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, hN.1 (hN.2.2.1 k hk g hg g₁ hg₁)⟩
      show R.p (g₁ - g) = 0
      rw [map_sub, hr.quot.cpt k hk g hg g₁ hg₁, sub_self]
    · intro γ hγ g hg g₁ hg₁
      refine ⟨?_, (L γ hγ g hg.2).2 g₁ hg₁⟩
      have e := hr.lie γ hγ g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (actsD_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, (C k hk g hg.2).2 g₁ hg₁⟩
      have e := hr.cpt k hk g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (acts_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
  have hKP : K ≠ P := by
    intro hKP
    haveI := hr.nontriv
    have hle : P ≤ LinearMap.ker R.p := hKP ▸ inf_le_left
    have hbot : P.map R.p = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro x hx
      simpa [Submodule.mem_comap] using hle hx
    exact bot_ne_top (hbot.symm.trans hr.quot.onto)

  have hirr := hr.irred (N.map R.p) ?_ ?_
  · rcases hirr with hbot | htop
    · intro f hf
      have : R.p f ∈ N.map R.p := Submodule.mem_map_of_mem hf
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      apply hsum N K hN hK hNP hKP
      refine le_antisymm (sup_le hN.1 inf_le_right) ?_
      intro g hg
      have hpg : R.p g ∈ N.map R.p := htop ▸ Submodule.mem_top
      obtain ⟨n₀, hn₀, hpn⟩ := hpg
      have hk : g - n₀ ∈ K := ⟨show R.p (g - n₀) = 0 by rw [map_sub, hpn, sub_self], P.sub_mem hg (hN.1 hn₀)⟩
      have := Submodule.add_mem_sup hn₀ hk
      simpa using this
  · intro γ hγ g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (L' γ hγ g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (L γ hγ n₀ (hN.1 hn₀)).1
    have e1 := hr.lie γ hγ g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.lie γ hγ n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.1 γ hγ n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩
  · intro k hk g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (C' k hk g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (C k hk n₀ (hN.1 hn₀)).1
    have e1 := hr.cpt k hk g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.cpt k hk n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.2 k hk n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩

end GlobalTheory.HoweRealKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  first | exact @GlobalTheory.HoweRealKer.main | exact GlobalTheory.HoweRealKer.main | (intros; apply GlobalTheory.HoweRealKer.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  first | exact @GlobalTheory.RepAdj.rep_adjoint_eq_inv | exact GlobalTheory.RepAdj.rep_adjoint_eq_inv | (intros; apply GlobalTheory.RepAdj.rep_adjoint_eq_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TypeExpand

theorem typeAt_expand : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  intro hU D θ V S M τ _ m k hk B hB φ hφ x g hg
  obtain ⟨H', _, _, σ, lam, ε, P, hen, hds, hPu, hPg, hx⟩ := hφ
  obtain ⟨v, -, ℓ, -, -, hsum⟩ := hx x
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hen
  subst hl he
  obtain ⟨U, hU'⟩ := hU _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P
    (M.fr_unit τ) hPu (M.fr_gram τ) hPg _ _ (M.σ τ) σ (M.ds τ) hds

  set A : ℕ → (M.H τ →ₗ[ℂ] M.H τ) := fun i =>
    ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (U (v i)) with hA
  have key : ∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      ℓ i (σ (P * h * P⁻¹) (v i)) =
        LinearMap.trace ℂ (M.H τ) ((M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) := by
    intro i h hh
    have e1 : (M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i =
        ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (M.rep τ h (U (v i))) := by
      ext w
      simp [hA]
    rw [e1, LinearMap.trace_smulRight]
    have e2 : M.rep τ h (U (v i)) = U (σ (P * h * P⁻¹) (v i)) := (hU' h hh (v i)).symm
    rw [e2]
    simp
  have h1 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
      (∑ j, φ (x * atTau θ V τ (k j)) *
        LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) := by
    refine hasSum_sum fun j _ => ?_
    refine HasSum.mul_right _ ?_
    have := hsum (k j) (hk j)
    refine this.congr_fun ?_
    intro i
    exact (key i (k j) (hk j)).symm
  have h2 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) (φ (x * atTau θ V τ g)) := by
    refine (hsum g hg).congr_fun ?_
    intro i
    rw [key i g hg, hB (A i) g hg]
  exact h2.unique h1

end GlobalTheory.TypeExpand

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelType_form_expands_along_dualFrame : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  first | exact @GlobalTheory.TypeExpand.typeAt_expand | exact GlobalTheory.TypeExpand.typeAt_expand | (intros; apply GlobalTheory.TypeExpand.typeAt_expand <;> assumption)
end
end

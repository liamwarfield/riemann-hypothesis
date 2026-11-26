module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Assembly
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.PsiVMulVec
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2LocT
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LevelCongruenceTypedPlaces
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2Loc
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TensInjHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelCongruenceOf
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def GlueHA : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    ∃ h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p) ∧
      ∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h = 1

def TensInj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (x y : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
    (∀ v : HeightOneSpectrum (𝓞 X.B.I.F), tensMap (E := X.B.I.E) (evalV X.B.I.F v) x =
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) y) → x = y

def LevelCongruenceLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset → (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem tens_lin {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : Fin X.B.I.n → X.B.I.E) (i : Fin X.B.I.n) :
    tensMap (E := X.B.I.E) (evalV X.B.I.F v) (lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h
      (ratV (Af X.B.I.F) x) i) =
    lin (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h)
      (ratV (Fv X.B.I.F v) x) i := by
  change tensMap (E := X.B.I.E) (evalV X.B.I.F v) (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h :
      GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Af X.B.I.F) (x j)) =
    ∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Fv X.B.I.F v) (x j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

theorem surjKH_of (hg : GlueHA) (hi : TensInj) : SurjKH := by
  intro D X w t htH htK
  classical
  obtain ⟨h, hT, hO⟩ := hg X t
  have hloc : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
    intro v
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      exact ⟨htH ⟨v, hv⟩, htK ⟨v, hv⟩⟩
    · rw [hO v hv]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))⟩
  refine ⟨h, ?_, ?_, hT⟩
  · unfold Hsub
    rw [mem_stabT]
    intro b
    funext i
    apply hi X
    intro v
    rw [tens_lin X v h]
    have hv := (hloc v).1
    unfold Hsub at hv
    rw [mem_stabT] at hv
    rw [hv b]
    simp only [ratV, tensMap_inclR]
  · exact Subgroup.mem_iInf.2 fun v => (hloc v).2

theorem conjugate_level_congruence_of (hl : LevelCongruenceLocal) : ConjugateLevelLocalCongruence := by
  intro D X hb hK hL w h _ hKf hp
  have hc : finHA X hb (X.xu w) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  obtain ⟨κ, hκ⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w))
  have hκf : finHA X hb κ = (finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w) := hκ
  have hκK : κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κ).1 ?_
    change finHA X hb κ ∈ _
    rw [hκf]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hKf) hc
  have hmem : κ ∈ X.K2 := by
    refine hl X hb hK hL κ hκK (fun p => ?_)
    obtain ⟨y, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hy⟩ := hp p
    refine ⟨k, hk, ?_⟩
    rw [hκf]
    simp only [map_mul, map_inv] at hy ⊢
    rw [← hy]
    group
  exact ⟨finHA X hb κ, ⟨κ, hmem, rfl⟩, by rw [hκf]; group⟩

theorem global_product_of_local (hg : GlueHA) (hi : TensInj) (hl : LevelCongruenceLocal) : GlobProd :=
  globProd_of compH_holds compK_holds k2uGrp_holds (surjKH_of hg hi) (conjugate_level_congruence_of hl)

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

theorem tens_repr {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] {ι : Type} (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (x : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (tensMap (E := E) φ x) i =
      φ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [tensMap, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem tensInj_holds : TensInj := by
  intro D X x y h
  let b := Module.Basis.ofVectorSpace X.B.I.F X.B.I.E
  apply (Algebra.TensorProduct.basis (Af X.B.I.F) b).repr.injective
  refine Finsupp.ext (fun i => FiniteAdeleRing.ext _ (fun v => ?_))
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr z i) (h v)
  simp only [tens_repr] at e
  exact e

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Glue

variable {D : D7} (X : HidaSetting D)

theorem glue_af (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F))) (a : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Fv X.B.I.F v)
    (c : X.B.I.F) (ha : ∀ v, v ∉ T → a v = evalV X.B.I.F v (algebraMap X.B.I.F (Af X.B.I.F) c)) :
    ∃ A : Af X.B.I.F, ∀ v, evalV X.B.I.F v A = a v := by
  have h1 : ∀ᶠ v in Filter.cofinite, (algebraMap X.B.I.F (Af X.B.I.F) c) v ∈ v.adicCompletionIntegers X.B.I.F :=
    (algebraMap X.B.I.F (Af X.B.I.F) c).2
  have hev : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers X.B.I.F := by
    filter_upwards [h1, T.eventually_cofinite_notMem] with v hv1 hv2
    rw [ha v hv2]
    exact hv1
  exact ⟨RestrictedProduct.mk a hev, fun v => rfl⟩

theorem glue_tens (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F)))
    (m : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c : X.B.I.E)
    (hm : ∀ v, v ∉ T → m v = inclR (Fv X.B.I.F v) c) :
    ∃ M : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, tensMap (E := X.B.I.E) (evalV X.B.I.F v) M = m v := by
  have : Module.Finite X.B.I.F X.B.I.E := Module.finite_of_finrank_eq_succ (n := 1) X.B.I.cm.deg2
  let b := Module.finBasis X.B.I.F X.B.I.E
  have key : ∀ i, ∃ A : Af X.B.I.F, ∀ v, evalV X.B.I.F v A =
      (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr (m v) i := fun i =>
    glue_af X T _ (b.repr c i) (fun v hv => by
      rw [hm v hv, AlgHom.commutes]
      simp [inclR, Algebra.TensorProduct.includeRight_apply])
  choose A hA using key
  refine ⟨(Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr.injective
  refine Finsupp.ext (fun i => ?_)
  rw [tens_repr, ← hA i v]
  congr 1
  exact congrFun ((Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.apply_symm_apply A) i

theorem glue_mat (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F)))
    (m : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
    (C : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (hm : ∀ v, v ∉ T → m v = C.map (inclR (Fv X.B.I.F v))) :
    ∃ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
      ∀ v, M.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v)) = m v := by
  have key : ∀ i j, ∃ a : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v,
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) a = m v i j := fun i j =>
    glue_tens X T (fun v => m v i j) (C i j) (fun v hv => by rw [hm v hv]; rfl)
  choose M hM using key
  exact ⟨Matrix.of M, fun v => Matrix.ext (fun i j => by simp [hM])⟩

theorem mat_inj (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    (h : ∀ v, M.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v)) = N.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v))) :
    M = N :=
  Matrix.ext (fun i j => tensInj_holds X _ _ (fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa using this))

theorem map_cT {R S : Type} [CommRing R] [Algebra X.B.I.F R] [CommRing S] [Algebra X.B.I.F S]
    (φ : R →ₐ[X.B.I.F] S) (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E)) :
    (Formalism.UG.cT (sigR R X.B.I.cm.sig) g * JR R X.B.I.J * g).map (tensMap (E := X.B.I.E) φ) =
      Formalism.UG.cT (sigR S X.B.I.cm.sig) (g.map (tensMap (E := X.B.I.E) φ)) * JR S X.B.I.J *
        g.map (tensMap (E := X.B.I.E) φ) := by
  have hcT : (Formalism.UG.cT (sigR R X.B.I.cm.sig) g).map (tensMap (E := X.B.I.E) φ) =
      Formalism.UG.cT (sigR S X.B.I.cm.sig) (g.map (tensMap (E := X.B.I.E) φ)) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, tensMap, PI.VolStabSW.CompGAux.tmap_sigR]
  have hJ : (JR R X.B.I.J).map (tensMap (E := X.B.I.E) φ) = JR S X.B.I.J := by
    ext i j
    simp [JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]
  rw [Matrix.map_mul, Matrix.map_mul, hcT, hJ]

end Glue

theorem glueHA_holds : GlueHA := by
  intro D X t
  classical
  let T := typSet X.B.I.F (D.host.g 0) (D.host.g 1)
  let gt : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := fun v =>
    if hv : v ∈ T then HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (t ⟨v, hv⟩) else 1
  have hgt : ∀ v, gt v ∈ HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J := by
    intro v
    by_cases hv : v ∈ T
    · simp only [gt, dif_pos hv]
      exact (show ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) from t ⟨v, hv⟩).2
    · simp only [gt, dif_neg hv]
      exact Subgroup.one_mem _
  have hout : ∀ v, v ∉ T → gt v = 1 := fun v hv => by simp only [gt, dif_neg hv]
  have h1 : ∀ (v : HeightOneSpectrum (𝓞 X.B.I.F)),
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) =
        (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (Fv X.B.I.F v)) := fun v =>
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  obtain ⟨M, hM⟩ := glue_mat X T (fun v => ((gt v : GL _ _) : Matrix _ _ _)) 1
    (fun v hv => by simp only [hout v hv, Units.val_one]; exact h1 v)
  obtain ⟨N, hN⟩ := glue_mat X T (fun v => (((gt v)⁻¹ : GL _ _) : Matrix _ _ _)) 1
    (fun v hv => by simp only [hout v hv, inv_one, Units.val_one]; exact h1 v)
  have hMN : M * N = 1 := mat_inj X _ _ (fun v => by
    rw [Matrix.map_mul, hM v, hN v, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := mat_inj X _ _ (fun v => by
    rw [Matrix.map_mul, hM v, hN v, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let G : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨M, N, hMN, hNM⟩
  have hG : G ∈ HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := by
    show Formalism.UG.cT (sigR (Af X.B.I.F) X.B.I.cm.sig) M * JR (Af X.B.I.F) X.B.I.J * M = JR (Af X.B.I.F) X.B.I.J
    apply mat_inj X
    intro v
    rw [map_cT X (evalV X.B.I.F v) M, hM v]
    have hv : Formalism.UG.cT (sigR (Fv X.B.I.F v) X.B.I.cm.sig) ((gt v : GL _ _) : Matrix _ _ _) *
        JR (Fv X.B.I.F v) X.B.I.J * ((gt v : GL _ _) : Matrix _ _ _) = JR (Fv X.B.I.F v) X.B.I.J := hgt v
    rw [hv]
    ext i j
    simp [JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]
  let hA : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := (⟨G, hG⟩ : ↥(HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hc : ∀ v, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) hA =
      (⟨gt v, hgt v⟩ : ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) := fun v =>
    Subtype.ext (Units.ext (hM v))
  refine ⟨hA, fun p => ?_, fun v hv => ?_⟩
  · rw [hc p.1]
    apply Subtype.ext
    simp only [gt]
    rw [dif_pos (show p.1 ∈ T from p.2)]
    rfl
  · rw [hc v]
    apply Subtype.ext
    exact hout v hv

theorem globProd_of_k2Loc (hl : LevelCongruenceLocal) : GlobProd := global_product_of_local glueHA_holds tensInj_holds hl

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def KgLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (κ : X.B.I.Gf), κ ∈ X.B.I.Kset →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) = 1) → κ ∈ X.B.I.Kg X.B.g

def LevelCongruenceTypedPlaces : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset →
    (∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ) = 1) →
    (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem level_local_of_typed (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : LevelCongruenceLocal := by
  intro D X hb hK hL κ hκ hloc
  classical
  obtain ⟨h, hT, hO⟩ := glueHA_holds X
    (fun p => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ))
  obtain ⟨κt, hκt⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb h
  have hκtf : finHA X hb κt = h := hκt
  have hκf : finHA X hb κ ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb κ hκ
  have hhK : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine Subgroup.mem_iInf.2 fun v => ?_
    have hv' : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
      by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
      · have e := hT ⟨v, hv⟩
        simp only at e
        rw [e]
        exact compK_holds X v _ hκf
      · rw [hO v hv]
        exact Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    exact hv'
  have hκtK : κt ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κt).1 ?_
    change finHA X hb κt ∈ _
    rw [hκtf]
    exact hhK
  have hrK : κt⁻¹ * κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb _).1 ?_
    change finHA X hb (κt⁻¹ * κ) ∈ _
    rw [finHA_mul, finHA_inv, hκtf]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhK) hκf
  have hrest : κt⁻¹ * κ ∈ X.B.I.Kg X.B.g := hg X hb _ hrK (fun p => by
    rw [finHA_mul, finHA_inv, map_mul, map_inv, hκtf, hT p]
    exact inv_mul_cancel _)
  have hκt2 : κt ∈ X.K2 := ht X hb hK hL κt hκtK (fun v hv => by rw [hκtf]; exact hO v hv)
    (fun p => by
      obtain ⟨κ', hκ', e⟩ := hloc p
      exact ⟨κ', hκ', by rw [hκtf, hT p]; exact e⟩)
  have hr2 : κt⁻¹ * κ ∈ X.K2 := (hL.1 _ hrest).1
  have hprod := hK.2.1 _ hκt2 _ hr2
  rwa [mul_inv_cancel_left] at hprod

theorem globProd_of_loc (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_k2Loc (level_local_of_typed hg ht)

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix

theorem g_cast_ne_zero {D : D7} (X : HidaSetting D) : (X.B.g : X.B.I.F) ≠ 0 := by
  rw [X.g_eq]
  push_cast
  exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)

theorem ginv_int {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)) :
    (algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹)) ∈ v.adicCompletionIntegers X.B.I.F := by
  rw [mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero] at hv
  unfold IsTyped at hv
  rw [not_or] at hv
  have hg : ((X.B.g : 𝓞 X.B.I.F)) ∉ v.asIdeal := by
    rw [X.g_eq]
    push_cast
    intro h
    rcases v.isPrime.mem_or_mem h with h | h
    exacts [hv.1 h, hv.2 h]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : algebraMap X.B.I.F (Fv X.B.I.F v) ((X.B.g : X.B.I.F)⁻¹) =
      (((X.B.g : X.B.I.F)⁻¹ : X.B.I.F) : v.adicCompletion X.B.I.F) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : v.valuation X.B.I.F (X.B.g : X.B.I.F) = 1 := by
    rw [show (X.B.g : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (X.B.g : 𝓞 X.B.I.F) by simp,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hg]
  rw [this, inv_one]

theorem smul_latLoc {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (hv : v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1))
    (u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (hu : u ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    (fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) * u i) ∈
      latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have := Submodule.smul_mem _ (⟨_, ginv_int X v hv⟩ : v.adicCompletionIntegers X.B.I.F) hu
  convert this using 1
  funext i
  rw [Pi.smul_apply, IsScalarTower.algebraMap_apply X.B.I.F (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    ← Algebra.smul_def]
  rfl

theorem kgLoc_holds : KgLoc := by
  intro D X hb κ hκ hT
  refine ⟨hκ, fun y hy => ?_⟩
  let c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := algebraMap X.B.I.F _ ((X.B.g : X.B.I.F)⁻¹)
  refine ⟨fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i, ?_, ?_⟩
  · apply PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective
    intro v
    have hy' := PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy v
    have hmat : (X.B.I.fmat κ).map (PI.FinKW.psiV X.B.I v) =
        ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
      change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb κ) :
        GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
          (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
      rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb κ, Matrix.map_map]
      rfl
    have hvec : PI.FinKW.vecV X.B.I v (fun i => c * ((X.B.I.fmat κ - 1) *ᵥ y) i) =
        fun i => algebraMap X.B.I.F (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((X.B.g : X.B.I.F)⁻¹) *
          ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ)) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v y) i := by
      funext i
      simp only [PI.FinKW.vecV, map_mul, c, AlgHom.commutes]
      congr 1
      have h1 := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat κ - 1) y i
      rw [← hmat, ← Matrix.map_one (PI.FinKW.psiV X.B.I v).toRingHom (map_zero _) (map_one _)]
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b)] at h1
      exact h1
    rw [hvec]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec]
      simp only [Pi.zero_apply, mul_zero]
      exact Submodule.zero_mem _
    · apply smul_latLoc X v hv
      have hK := compK_holds X v (finHA X hb κ) (finHA_mem_Kf X hb κ hκ)
      have hm := (hK (PI.FinKW.vecV X.B.I v y)).1 hy'
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Submodule.sub_mem _ hm hy'
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, c, ← mul_assoc]
    rw [show ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = algebraMap X.B.I.F _ (X.B.g : X.B.I.F) by simp,
      ← map_mul, mul_inv_cancel₀ (g_cast_ne_zero X), map_one, one_mul]

theorem globProd_of_k2LocT (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_loc kgLoc_holds ht

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix
open Classical

section Idem

variable {D : D7} (X : HidaSetting D)

def idemAf (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Af X.B.I.F :=
  RestrictedProduct.mk (fun v => if v = p then (1 : Fv X.B.I.F v) else 0)
    (Filter.Eventually.of_forall (fun v => by
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _))

theorem idemAf_int (p : HeightOneSpectrum (𝓞 X.B.I.F)) : idemAf X p ∈ Formalism.UG.intAd X.B.I.F := by
  intro v
  show (if v = p then (1 : Fv X.B.I.F v) else 0) ∈ v.adicCompletionIntegers X.B.I.F
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def idemT (p : HeightOneSpectrum (𝓞 X.B.I.F)) : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  ⟨(1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p,
    Subring.subset_closure (Or.inr ⟨⟨idemAf X p, idemAf_int X p⟩, rfl⟩)⟩

theorem psiV_idemT (p v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.psiV X.B.I v ((idemT X p : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      if v = p then 1 else 0 := by
  show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v) (AlgHom.id X.B.I.F X.B.I.E))
      ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F))
        ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] idemAf X p)) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.B.I.F v (idemAf X p) = if v = p then 1 else 0 := rfl
  rw [he]
  split_ifs
  · exact Algebra.TensorProduct.one_def.symm
  · exact TensorProduct.zero_tmul _ _

theorem fmat_psiV (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (X.B.I.fmat x).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
  change _ = (((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.tf X.B.I hb x) :
    GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map
      (tensMap (E := X.B.I.E) (evalV X.B.I.F v))
  rw [PI.MassDataKppVolLemmas.Bridge_mat X.B.I hb x, Matrix.map_map]
  rfl

theorem psiV_mulVec (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (i : Fin X.B.I.n) :
    PI.FinKW.psiV X.B.I v (((X.B.I.fmat x - 1) *ᵥ w) i) =
      ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb x)) : GL (Fin X.B.I.n) _) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
          PI.FinKW.vecV X.B.I v w) i := by
  rw [← fmat_psiV X hb x v]
  have h := RingHom.map_mulVec (PI.FinKW.psiV X.B.I v).toRingHom (X.B.I.fmat x - 1) w i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext a b
  simp [Matrix.sub_apply, Matrix.one_apply]

end Idem

theorem level_congruence_typed_places : LevelCongruenceTypedPlaces := by
  intro D X hb hK hL κ hκ hO hloc
  classical
  choose κ' hκ' heq using hloc
  have decomp : ∀ w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (X.B.I.fmat κ - 1) *ᵥ w = ∑ p : TypX X, idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w) := by
    intro w
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective X.B.I
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, psiV_mulVec X hb κ v w i, Finset.sum_apply, map_sum]
    simp only [Pi.smul_apply]
    have hs : ∀ p : TypX X, PI.FinKW.psiV X.B.I v ((idemT X p.1 • ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) i) =
        (if v = p.1 then 1 else 0) * ((((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
          (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb (κ' p))) : GL (Fin X.B.I.n) _) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
            PI.FinKW.vecV X.B.I v w) i := by
      intro p
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, psiV_idemT, psiV_mulVec X hb (κ' p) v w i]
    simp only [Pi.smul_apply] at hs
    rw [Finset.sum_congr rfl (fun p _ => hs p)]
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · rw [Finset.sum_eq_single (⟨v, hv⟩ : TypX X)]
      · rw [if_pos rfl, one_mul, ← heq ⟨v, hv⟩, sub_self]
      · intro p _ hp
        rw [if_neg (fun h => hp (Subtype.ext h.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero (fun p _ => by rw [if_neg (fun h => hv (by rw [h]; exact p.2)), zero_mul])]
      rw [hO v hv]
      have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
          GL (Fin X.B.I.n) _) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
      rw [this, sub_self, Matrix.zero_mulVec, Pi.zero_apply, sub_zero]
  have hmem : ∀ (S : Set (Formalism.L2.SG.HidaSetting.VA X.B.I)) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ p : TypX X, InMod X.B.I X.B.g S ((X.B.I.fmat (κ' p) - 1) *ᵥ w)) →
        InMod X.B.I X.B.g S ((X.B.I.fmat κ - 1) *ᵥ w) := by
    intro S w h
    unfold InMod at h ⊢
    rw [decomp w]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (h p))
  refine ⟨hκ, ?_, ?_, ?_⟩
  · exact fun a => hmem _ _ (fun p => (hκ' p).2.1 a)
  · exact hmem _ _ (fun p => (hκ' p).2.2.1)
  · exact fun i => hmem _ _ (fun p => (hκ' p).2.2.2 i)

theorem globProd_holds : GlobProd := globProd_of_k2LocT level_congruence_typed_places

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.KSpTop
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOfParts
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOf
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem inLevelSAt_of_parts (hLS : LevelSAll) (a1 : KSpCompact) (a2 : KSpOpen) (b1 : CMInst) (b2 : FrameStd)
    (b3 : LatAdapted) (b4 : ProdNH) (b5 : GlobFromParts) (c1 : HaarIdxLoc) (c2 : HaarIdxGlob) (c3 : LocLevi)
    (c4 : GlobProd) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of (typedNe_of a1 a2) (b5 hLS b1 b2 b3 b4) (ratioH_of c1 c2 c3 c4)

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ProdNH
noncomputable section

namespace MassDataLevelSSteps.ProdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory NumberField
  IsDedekindDomain Topology PI.AdicCompletionValuation
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R]
    {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hcont : Continuous fun g : HA R σ J => g • ratTup (F := F) R X0 := by
    show Continuous fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | g • ratTup (F := F) R X0 = ratTup (F := F) R X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

instance secondCountable_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

theorem prodNH_of {r : ℕ} (P : Frame E n r) (M : MeasW σ J P) (hM : M.IsTextNorm) :
    IsProdNH F E σ n J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) M.μSf M.μNf M.μHf := by
  obtain ⟨-, -, hH, -, -, -, -, -, -, -, hS⟩ := hM
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT σ J (Af F) (tupH P)
  have : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hH
  have : SecondCountableTopology (HA (Af F) σ J) := secondCountable_HAf σ J
  have : SecondCountableTopology (Hsub (Af F) σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : WeaklyLocallyCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : IsFiniteMeasureOnCompacts M.μHf := inferInstance
  have : IsLocallyFiniteMeasure M.μHf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : SigmaFinite M.μHf := sigmaFinite_of_locallyFinite
  have : SFinite (amb M.μHf) := inferInstance
  have hmul : Measurable fun p : HA (Af F) σ J × HA (Af F) σ J => p.1 * p.2 := measurable_mul
  intro f hf
  have e1 : ∫⁻ k, f (k : HA (Af F) σ J) ∂M.μSf = ∫⁻ x, f x ∂(amb M.μSf) :=
    (lintegral_map hf measurable_subtype_coe).symm
  rw [e1, hS, lintegral_map hf hmul, lintegral_prod (fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2)) (hf.comp hmul).aemeasurable]
  have hin : Measurable fun x : HA (Af F) σ J => ∫⁻ y, f (x * y) ∂(amb M.μHf) :=
    Measurable.lintegral_prod_right' (f := fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2))
      (hf.comp hmul)
  rw [lintegral_map hin measurable_subtype_coe]
  refine lintegral_congr fun m => ?_
  exact lintegral_map (hf.comp (measurable_const_mul _)) measurable_subtype_coe

end MassDataLevelSSteps.ProdW

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

theorem prodNH_holds : ProdNH := by
  intro D X w
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  exact ProdW.prodNH_of X.B.I.cm.sig X.B.I.J _ (X.measW w) (X.measW_norm w)

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobFromParts
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem globFromParts_holds : GlobFromParts := by
  intro hLS h1 h2 h3 h4 D X hb _ _ w
  obtain ⟨hCM, hJ⟩ := h1 X
  obtain ⟨T, hT⟩ := h2 X w
  obtain ⟨ΛX, ΛW, ΛY, hA, hK⟩ := h3 X w
  obtain ⟨-, -, hHf, -, -, hNf, hSf, -⟩ := X.measW_norm w
  have key := (hLS X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hJ hJ D.R.rS (frameOf X w) T hT
    ΛX ΛW ΛY hA (X.measW w).μNf hNf (X.measW w).μHf hHf).2 (X.measW w).μSf ⟨hSf, h4 X w⟩
  simp only [KS, NO, KH, Subgroup.mem_inf, hK, SetLike.coe_mem, true_and] at key
  unfold muSf muNf muHf
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal key

end MassDataLevelSSteps
end
end

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem levelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split

theorem inLevelSAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of_parts levelSAll_holds kSpCompact_holds kSpOpen_holds cmInst_holds frameStd_holds
    latAdapted_holds prodNH_holds globFromParts_holds haarIdxLoc_holds haarIdxGlob_holds locLevi_holds
    globProd_holds

end MassDataLevelSSteps
end
end

theorem level_s_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataLevelSSteps.inLevelSAt_holds

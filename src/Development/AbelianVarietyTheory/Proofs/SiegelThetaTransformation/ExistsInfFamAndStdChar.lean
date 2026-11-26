module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedPullbackMulNReadsTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslation
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem exists_infFam_and_stdChar : ∀ D : D7, (∃ θ : InfFam D, IsInfFam θ) ∧ ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) :=
  fun D => ⟨GlobalTheory.DualPairCompare.exists_infFam D, GlobalTheory.StdAdelicChar.exists_isStdChar D⟩

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.CongTop

variable {D : D7}

theorem fmt_eq (V : HSp D) (g : GA D V) : fmt V g = (finHom V g).1 := rfl

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt_eq, map_one, Units.val_one]

theorem fmt_mul (V : HSp D) (g h : GA D V) : fmt V (g * h) = fmt V g * fmt V h := by
  rw [fmt_eq, map_mul, Units.val_mul, fmt_eq, fmt_eq]

theorem isMov_iff (V : HSp D) (L : Lt D.host.E V.rank) (k : GA D V) :
    IsMov (fmt V k) L L ↔ (∀ u ∈ hatV L, fmt V k *ᵥ u ∈ hatV L) ∧ ∀ u ∈ hatV L, fmt V k⁻¹ *ᵥ u ∈ hatV L := by
  constructor
  · intro h
    refine ⟨fun u hu => (h _).2 ⟨u, hu, rfl⟩, fun u hu => ?_⟩
    obtain ⟨u₀, h0, rfl⟩ := (h u).1 hu
    rwa [Matrix.mulVec_mulVec, ← fmt_mul, inv_mul_cancel, fmt_one, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu
      refine ⟨_, h2 u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec]
    · rintro ⟨u₀, h0, rfl⟩
      exact h1 _ h0

noncomputable def congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) : Subgroup (GA D V) where
  carrier := {k | CongK V L M k}
  one_mem' := by
    refine ⟨(isMov_iff V L 1).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u _ => ⟨0, zero_mem _, ?_⟩⟩
    · rwa [fmt_one, Matrix.one_mulVec]
    · rwa [inv_one, fmt_one, Matrix.one_mulVec]
    · rw [fmt_one, Matrix.one_mulVec, sub_self, nsmul_zero]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    rw [isMov_iff] at ha hb
    refine ⟨(isMov_iff V L _).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · rw [fmt_mul, ← Matrix.mulVec_mulVec]
      exact ha.1 _ (hb.1 _ hu)
    · rw [_root_.mul_inv_rev, fmt_mul, ← Matrix.mulVec_mulVec]
      exact hb.2 _ (ha.2 _ hu)
    · obtain ⟨x, hx, ex⟩ := ha' _ (hb.1 _ hu)
      obtain ⟨y, hy, ey⟩ := hb' _ hu
      refine ⟨x + y, add_mem hx hy, ?_⟩
      rw [fmt_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← ex, ← ey, sub_add_sub_cancel]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    rw [isMov_iff] at ha
    refine ⟨(isMov_iff V L _).2 ⟨ha.2, by rw [inv_inv]; exact ha.1⟩, fun u hu => ?_⟩
    obtain ⟨x, hx, ex⟩ := ha' _ (ha.2 _ hu)
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec] at ex
    rw [neg_nsmul, ← ex, neg_sub]

theorem isOpen_congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) (hM : 0 < M) :
    IsOpen (congSub V L M : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hn : {m : Matrix (Fin V.rank) (Fin V.rank) (AfE D) | ∀ z ∈ hatV L, ∃ y ∈ hatV L, m *ᵥ z - z = M • y} ∈
      nhds (1 : Matrix (Fin V.rank) (Fin V.rank) (AfE D)) :=
    GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp M hM
  have hc : Continuous (fmt V) := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [fmt_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, fmt_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩
  refine ⟨(isMov_iff V L k).2 ⟨fun y hy => ?_, fun y hy => ?_⟩, hk1⟩
  · obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy
  · obtain ⟨w, hw, h⟩ := hk2 y hy
    rw [Function.comp_apply] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy

theorem isClosed_GinfC (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem isClosed_GfC (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)
  haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GfC V : Set (GA D V)) = {g | (infHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  have hm : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_map (GlobalTheory.Member.continuous_infPart D)) continuous_const

theorem exists_compact (V : HSp D) (L : Lt D.host.E V.rank) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, IsMov (fmt V k) L L → (k ∈ GfC V ∨ V.gram = 1) → k ∈ C := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp' := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp' (tauE D ρ)).2.2.2.2 h)
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E L hfg hsp
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k h1 h2 => hKe k fun i j =>
    hCe' _ (hCe (fmt V k) ((isMov_iff V L k).1 h1).1 i j) fun ρ => ?_⟩
  have hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
    rcases h2 with h2 | h2
    · have h3 : (infHom V k).1 = 1 := congrArg Units.val (show infHom V k = 1 from h2)
      have h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ) := rfl
      rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
    · have h3 : gramAt D V ρ = 1 := by
        unfold gramAt
        rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]
      have h4 := hu ρ k
      rw [h3, Matrix.mul_one] at h4
      exact Matrix.mem_unitaryGroup_iff'.2 h4
  exact entry_norm_bound_of_unitary hU i j

theorem adelicUnitary_top_cong : ∀ (D : D7) (V : HSp D), IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsClosed (GinfC V : Set (GA D V)) ∧ ∀ (L : Lt D.host.E V.rank) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → 0 < M → ∃ K : Subgroup (GA D V), (∀ k, k ∈ K ↔ CongK V L M k) ∧ IsOpen (K : Set (GA D V)) ∧ IsCompact ((K : Set (GA D V)) ∩ GfC V) ∧ (V.gram = 1 → IsCompact (K : Set (GA D V))) := by
  intro D V
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine ⟨i0, i1, i2, i3, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram, isClosed_GinfC V, ?_⟩
  rintro L M ⟨hfg, hsp⟩ hM
  have ho := isOpen_congSub V L M hfg hsp hM
  have hcl : IsClosed (congSub V L M : Set (GA D V)) := Subgroup.isClosed_of_isOpen _ ho
  obtain ⟨C, hC, hCm⟩ := exists_compact V L hfg hsp
  refine ⟨congSub V L M, fun _ => Iff.rfl, ho, ?_, fun hg => ?_⟩
  · exact hC.of_isClosed_subset (hcl.inter (isClosed_GfC V)) fun k hk => hCm k hk.1.1 (Or.inl hk.2)
  · exact hC.of_isClosed_subset hcl fun k hk => hCm k hk.1 (Or.inr hg)

end GlobalTheory.Ker.CongTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormMatch

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P = 1) (hP' : P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  subst hP hP'
  rw [sum_four_eq_trace, sum_four_eq_trace]
  have hk1 : (k.map σ)ᵀ * k = 1 := by simpa only [Matrix.mul_one] using hk
  have hk2 : k * (k.map σ)ᵀ = 1 := mul_eq_one_comm.mp hk1
  have hg' : ∀ R : Matrix (Fin m) (Fin n) A, (g.map σ)ᵀ * (Q * (g * R)) = Q * R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.one_mul, Matrix.mul_assoc, hg']
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hk2, Matrix.mul_one]

theorem sum_one_four {A : Type} [CommRing A] {m n : ℕ} (u : Fin m → Fin n → A) (Q : Fin m → Fin m → A)
    (x : Fin m → Fin n → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, (1 : Matrix (Fin n) (Fin n) A) a b * u c b * Q c d * x d a =
      ∑ k, ∑ d, ∑ c, x d k * Q c d * u c k := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

variable {D : D7} {S T : HSp D}

theorem hO_actO (hS : S.gram = 1) (h : GA D S) (g : GA D T) (w w' : WO S T) :
    hO S T (actO S T h g w) (actO S T h g w') = hO S T w w' := by
  have hinv : ((HSpace.gram S)⁻¹).map (incA D) = 1 := by
    rw [hS, Matrix.inv_eq_left_inv (Matrix.mul_one 1), Matrix.map_one _ (map_zero _) (map_one _)]
  have key := sum_unitary (cA D) ((HSpace.gram T).map (incA D)) (Formalism.L2.Theta.mt T g)
    (((HSpace.gram S)⁻¹).map (incA D)) 1 (Formalism.L2.Theta.mt S h⁻¹) hinv rfl ?hg ?hk w w'
  · unfold hO actO
    simpa only [Matrix.map_apply] using key
  · have hu := g.2
    exact hu
  · have hu : ((Formalism.L2.Theta.mt S h⁻¹).map (cA D))ᵀ * (HSpace.gram S).map (incA D) * Formalism.L2.Theta.mt S h⁻¹ =
        (HSpace.gram S).map (incA D) := (h⁻¹).2
    have h1 : (HSpace.gram S).map (incA D) = 1 := by
      rw [hS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hu
    exact hu

theorem hRat_eq (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = ∑ k, herm C.X.Gm (y k) (y' k) := by
  unfold GlobalTheory.LatVac.hRat ReciprocityTheory.ChartRestriction.G.FD.herm
  rw [C.m.gS, C.m.gT, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_single k (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  have hs : star (y' k c) = ReciprocityTheory.ChartRestriction.G.FD.cc (y' k c) := rfl
  rw [hs]
  ring

theorem sum_EF (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ)) := by
  simp only [GlobalTheory.ThFr.EF_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.mul_sum, ← hRat_eq C, C.m.ka, Algebra.trace_trace,
    show -(2 * D.host.xi0 / 2) * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = -(D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ) by ring,
    map_neg]

theorem symplO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  rw [← (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (ratW T S M) (ratW T S N)]
  have h2 : symplOH S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) :=
    GlobalTheory.OrientedFormLaws.symplOH_rat M N
  rw [h2, ← map_add (f := _)]
  congr 1
  ring

theorem re_match {m n : ℕ} (ξ : ℂ) (Q : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ k, 2 * (conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k))).re =
      -(2 * (ξ * ∑ k, ∑ d, ∑ c, x d k * Q c d * conj (y c k)).re) := by
  have key : ∀ k, conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k)) =
      conj (-ξ * ∑ a, ∑ b, x a k * Q b a * conj (y b k)) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_neg]
  simp only [key, Complex.conj_re, neg_mul, Complex.neg_re, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum]

theorem EFR_realPt (C : Ctx S T) (w w' : WO S T) :
    EFR C.X (C.realPt w) (C.realPt w') = -omO S T (piW C.θ T S w) (piW C.θ T S w') := by
  rw [omO_apply, ← Finset.sum_neg_distrib]
  unfold EFR Ctx.realPt compAt
  rw [← C.m.e.sum_comp]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hS1 : gramAt D S τ = 1 := by
    unfold gramAt
    rw [C.m.gS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hom : -omAt S T τ (piW C.θ T S w τ) (piW C.θ T S w' τ) = ∑ k, 2 * (conj (-(tauE D τ D.host.xi0)) *
      ∑ a, ∑ b, conj (piW C.θ T S w τ a k) * conj (gramAt D T τ b a) *
        conj (conj (piW C.θ T S w' τ b k))).re := by
    rw [re_match (tauE D τ D.host.xi0) (gramAt D T τ) (piW C.θ T S w τ) (piW C.θ T S w' τ), neg_inj]
    unfold omAt hAt
    have h4 := GlobalTheory.OrientedChar.trace_four ((gramAt D S τ)⁻¹) (piW C.θ T S w' τ) (gramAt D T τ) (piW C.θ T S w τ)
    have h5 := sum_one_four (fun c b => starRingEnd ℂ (piW C.θ T S w' τ c b)) (gramAt D T τ) (piW C.θ T S w τ)
    rw [h4, hS1, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
    exact congrArg (fun s => 2 * (tauE D τ D.host.xi0 * s).re) h5
  rw [hom]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : -(2 * D.host.xi0 / 2) = -D.host.xi0 := by ring
  simp only [Equiv.symm_apply_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, C.m.e_emb τ,
    NumberField.ComplexEmbedding.conjugate_coe_eq, C.m.ka, C.m.gT, Matrix.transpose_apply, Matrix.map_apply,
    hx, map_neg]
  rfl

theorem symplOH_finW (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    symplOH S T (finW S T y) (finW S T y') = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ))) := by
  have hf : ∀ z : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T z = GlobalTheory.LatVac.finTens 1 zᵀ :=
    fun z => rfl
  have h := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (finW S T y) (finW S T y')
  rw [hf, hf, GlobalTheory.LatVac.symplO_finTens] at h
  simp only [one_mul] at h
  rw [hf, hf]
  have key : ∀ X Y : AF D.host.F, X + X = Y + Y → X = Y := by
    intro X Y hXY
    have h2 : (2 : D.host.F) • X = (2 : D.host.F) • Y := by rw [two_smul, two_smul, hXY]
    have h3 := congrArg (fun Z => (2 : D.host.F)⁻¹ • Z) h2
    simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), one_smul] using h3
  have hp : ∀ u v : Af D.host.F, pairA D.host.F 0 u + pairA D.host.F 0 v = pairA D.host.F 0 (u + v) := by
    intro u v
    unfold pairA
    exact Prod.ext (add_zero _) rfl
  apply key
  rw [h, hp, ← map_add (f := _)]
  congr 2
  ring

theorem forms_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  intro D S T C
  have hadd := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have halt := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T
  have htr : ∀ t : D.host.F, Algebra.trace ℚ D.host.F (1 / 2 * t) = 1 / 2 * Algebra.trace ℚ D.host.F t := by
    intro t
    rw [show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, halt.2.2.2.1, fun w w' w'' => ⟨halt.1 w w' w'', halt.2.2.1 w w'⟩, ?_, ?_⟩
  · intro y y' t ht
    rw [symplO_rat] at ht
    have : Nontrivial (AF D.host.F) := by
      unfold AF AdeleRing
      infer_instance
    rw [sum_EF C, (algebraMap D.host.F (AF D.host.F)).injective ht]
  · intro w w' hw _
    rw [GlobalTheory.OrientedChar.char_symplOH D C.θ C.ψ C.inf C.std S T w w' (Or.inl hw), EFR_realPt C]
    congr 1
    push_cast
    ring
  · intro y y'
    rw [symplOH_finW, GlobalTheory.StdRat.stdChar_fin_rat D C.ψ C.std, sum_EF C, htr]
    congr 1
    push_cast
    ring
  · intro w u hw hu
    have h0 : symplOH S T w u = 0 := hadd.2.2.2.2.2.2.2.2 w u hw hu
    have h1 : symplO S T w u = 0 := by rw [← hadd.2.2.2.1 w u, h0, add_zero]
    exact ⟨h1, by rw [halt.2.2.1 u w, h1, neg_zero]⟩
  · intro h g w w'
    unfold symplO
    rw [hO_actO C.m.gS]
  · intro y
    refine ⟨?_, finRat_inf S T yᵀ, ?_, ?_⟩
    · funext σ k a
      unfold Ctx.realPt compAt
      obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
      rw [Equiv.symm_apply_apply]
      have e := congrFun (congrFun (congrFun (piW_ratW C.inf S T yᵀ) τ) a) k
      simp only [Matrix.map_apply, embR, C.m.e_emb τ, NumberField.ComplexEmbedding.conjugate_coe_eq]
      congr 1
    · show (ratW T S yᵀ - finW S T y).map (finPart D) = 0
      have e := finRat_fin S T yᵀ
      ext i j
      have e2 := congrFun (congrFun e i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at e2 ⊢
      rw [← e2]
      exact sub_self _
    · intro y'
      ext a k
      simp only [finW, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]

end GlobalTheory.FormMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticCharacter_real_finite_points_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  first | exact @GlobalTheory.FormMatch.forms_match | exact GlobalTheory.FormMatch.forms_match | (intros; apply GlobalTheory.FormMatch.forms_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D}

theorem EFR_conj (C : Ctx S T) (x y : RW T S) :
    EFR C.X (fun σ k a => conj (x (C.m.e.symm σ) a k) : WR C.X S.rank) (fun σ k a => conj (y (C.m.e.symm σ) a k)) =
      -omO S T x y := by
  simp only [EFR, hermC, omO, LinearMap.mk₂_apply, formAt]
  rw [← C.m.e.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.symm_apply_apply, C.m.e_emb, C.m.ka, C.m.gT, C.m.gS, inv_one,
    ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply, RCLike.conj_conj]
  have hx : (-(2 * D.host.xi0 / 2)) = -D.host.xi0 := by ring
  have hone : ∀ F : Fin S.rank → Fin S.rank → ℂ,
      ∑ a, ∑ b, tauE D τ ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) a b) * F a b = ∑ a, F a a := by
    intro F; simp [Matrix.one_apply]
  rw [hx]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hone, ← Complex.re_sum, ← Finset.mul_sum]
  have hc : conj (tauE D τ (-D.host.xi0)) *
      ∑ k, ∑ a, conj (x τ a k) * ∑ b, conj (tauE D τ (T.gram b a)) * y τ b k =
      conj (-(tauE D τ D.host.xi0 *
        ∑ k, ∑ b, conj (y τ b k) * ∑ a, tauE D τ (T.gram b a) * x τ a k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_mul, map_sum, RCLike.conj_conj, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hc, Complex.conj_re, Complex.neg_re]
  ring

theorem pi_lineAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  obtain ⟨-, -, h⟩ := isLineAt_lineAt hθ τ z
  funext τ' i j
  have h1 := congrFun (congrFun (h 1 τ') i) j
  rw [Pi.single_apply]
  split_ifs at h1 ⊢ with hτ
  · rw [Complex.ofReal_one, one_smul] at h1
    exact h1
  · exact h1

theorem single_conj (C : Ctx S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) =
      fun σ k a => conj (piW C.θ T S (lineAt C.θ τ z 1) (C.m.e.symm σ) a k) := by
  rw [pi_lineAt C.inf]
  funext σ k a
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> simp

theorem dRho_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  intro D S T C f hf τ z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  have hθ := C.inf
  have hψ := C.std
  have hD' : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ),
      dRho (heisO C.ψ S T) C.θ τ z g =
        hD (iotaW σ T S) (piW C.θ T S) (omO S T) (piW C.θ T S (lineAt C.θ τ z 1)) g := by
    intro τ z g
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ z)]
  have hsm : ∀ g, C.IsTh g → Sm (iotaW σ T S) g := fun g hg => theta_sm hσ hg
  have hform : ∀ g, C.IsTh g → ∀ (u : RW T S) (w : WO S T),
      hD (iotaW σ T S) (piW C.θ T S) (omO S T) u g w =
        -(Real.pi * Complex.I) * (omO S T (piW C.θ T S w) u : ℝ) * g w +
          fderiv ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 u :=
    fun g hg u w => hD_eq_fderiv _ _ _ g (hsm g hg) u w
  have hdiff : ∀ g, C.IsTh g → ∀ w : WO S T,
      DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun g hg w => ((hsm g hg w).differentiable (by simp)) 0
  refine ⟨theta_dRho hθ hψ τ z hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0
    rw [map_zero, heisO_zero, ← dRho_eq_dLine] at h
    exact h
  · intro f' hf'
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f' hf', hform (f + f') (theta_add hf hf')]
    rw [show (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        (fun x => f (w + iotaW σ T S x)) + (fun x => f' (w + iotaW σ T S x)) from rfl,
      fderiv_add (hdiff f hf w) (hdiff f' hf' w)]
    simp only [Pi.add_apply, _root_.add_apply]
    ring
  · intro a
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform (a • f) (theta_smul a hf)]
    rw [show (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        (fun x => a * f (w + iotaW σ T S x)) from rfl, fderiv_const_mul (hdiff f hf w)]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
    ring
  · intro z'
    have hadd : piW C.θ T S (lineAt C.θ τ (z + z') 1) =
        piW C.θ T S (lineAt C.θ τ z 1) + piW C.θ T S (lineAt C.θ τ z' 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, e, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f hf, hform f hf, hadd, map_add (f := _),
      ContinuousLinearMap.map_add]
    push_cast
    ring
  · intro t
    have hs : piW C.θ T S (lineAt C.θ τ ((t : ℂ) • z) 1) = t • piW C.θ T S (lineAt C.θ τ z 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp [Complex.real_smul]
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform f hf, hs, map_smul, ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · intro u hu
    exact GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f
  · intro τ' z'
    have hskew : ∀ u v : RW T S, omO S T v u = -omO S T u v := by
      intro u v
      have h := omO_self hσ (u + v)
      simp only [map_add (f := _), LinearMap.add_apply, omO_self hσ, zero_add, add_zero] at h
      linarith
    simp only [hD']
    rw [heisenberg_derivative_commutator (WO S T) (RW T S) (iotaW σ T S) (piW C.θ T S) (omO S T)
      (hσ.pi_iota T S) (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) hskew f (hsm f hf),
      single_conj C τ z, single_conj C τ' z', EFR_conj]
    congr 1
    push_cast
    ring

end GlobalTheory.Ker.HeisDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_thetaFunction_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  first | exact @GlobalTheory.Ker.HeisDeriv.dRho_laws | exact GlobalTheory.Ker.HeisDeriv.dRho_laws | (intros; apply GlobalTheory.Ker.HeisDeriv.dRho_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabOpen

noncomputable def stab {D : D7} (V : HSp D) (L : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) :
    Subgroup (GA D V) where
  carrier := {h | ∀ y, y ∈ L ↔ (finHom V h).1.mulVec y ∈ L}
  one_mem' := fun y => by rw [map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    rw [ha ((finHom V a⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

theorem isOpen_stab_latHat : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  intro D V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have e : Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) =
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    rfl
  rw [e]
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp 1 one_pos
  have hc := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [map_one, Units.val_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, map_one, Units.val_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds (stab V (GlobalTheory.AdLat.hat D.host.F
    (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))) (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end GlobalTheory.StabOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_stabilizer_completedLattice_adelicUnitary : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  first | exact @GlobalTheory.StabOpen.isOpen_stab_latHat | exact GlobalTheory.StabOpen.isOpen_stab_latHat | (intros; apply GlobalTheory.StabOpen.isOpen_stab_latHat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem reads_isUUOver_isVtOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL N hN θ hθ
  have hpv : ∀ (n : ℕ) (a : Fin r → E), pv X idx x ((n : E) • a) = (n : ℂ) • pv X idx x a := by
    intro n a
    rw [(hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.1]
    funext j
    simp
  have hfk : ∀ (φ : (Fin g → ℂ) → ℂ) (a : Fin r → E),
      Dict.fock X bas idx x (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z)) =
        fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z) := by
    intro φ a
    rw [hpv]
    exact (fock_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx 1 φ).2.2.1 N _
  obtain ⟨Φ, he, -, hlat, -, -, hrd, hf⟩ := GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha =>
    (GlobalTheory.AnVal.chi_eq_sign E H Dw l Xo c y g _ e Φ a ha).1
  have htw : ∀ α₀ α s₁, α₀.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ →
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α
        (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd (ptO Xo y.x) Xo.univ.t.G).left) →
      IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G (ptO Xo y.x) N)
        (snd (ptO Xo y.x) Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α y.s s₁ →
      A.Reads ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
    intro α₀ α s₁ hg hn hc ht
    exact (hrd _ _ _).1
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr N α₀ α y.s s₁ θ hg hn hc ht ((hrd _ _ _).2 hθ))
  have hsy : ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) →
      ∀ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (A.ex (pv X idx x a)) U →
      ∀ (s s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (φ : (Fin g → ℂ) → ℂ),
      IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U s s' →
      A.Reads ((N : ℤ) ^ 2) s (fun z => φ ((N : ℂ) • z)) →
      A.Reads ((N : ℤ) ^ 2) s'
        (fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z)) := by
    rintro a ⟨u, hu, hau⟩ U hU s s' φ hA hs'
    have h2 : ((N ^ 2 : ℕ) : ℂ) • pv X idx x a = (2 : ℂ) • pv X idx x u := by
      have h3 := hpv 2 u
      rw [← hpv, Nat.cast_smul_eq_nsmul, hau, ← Nat.cast_smul_eq_nsmul E, h3]
      norm_num
    rw [← he] at hU
    have h4 := GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hχ ((N : ℤ) ^ 2) (N ^ 2) U
      (pv X idx x a) (pv X idx x u) s s' _ hN.pow ((hlat _).2 ⟨u, hu, rfl⟩) h2 hU hA ((hrd _ _ _).2 hs')
    have h5 := hf (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z))
    rw [Nat.cast_pow, hfk] at h5
    rw [h5] at h4
    exact (hrd _ _ _).1 h4
  refine ⟨?_, ?_⟩
  · rintro a₁ a₂ h₁ h₂ F ⟨α₀, α, s₁, s₂, U₁, U₂, hg, hn, hc, ht, hU₁, hA₁, hU₂, hA₂⟩
    exact hsy a₂ h₂ U₂ hU₂ s₂ F _ hA₂ (hsy a₁ h₁ U₁ hU₁ s₁ s₂ _ hA₁ (htw α₀ α s₁ hg hn hc ht))
  · rintro a h t F ⟨t', α₀, α, s₁, U, -, rfl, hg, hn, hc, ht, hU, hA⟩
    exact hsy a h U hU s₁ F _ hA (htw α₀ α s₁ hg hn hc ht)

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_read_as_translates_at_scaled_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  first | exact @GlobalTheory.Dict.reads_isUUOver_isVtOver | exact GlobalTheory.Dict.reads_isUUOver_isVtOver | (intros; apply GlobalTheory.Dict.reads_isUUOver_isVtOver <;> assumption)
end
end

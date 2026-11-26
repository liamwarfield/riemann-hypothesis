module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitSmul

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective
noncomputable section

namespace MassDataIdxSplit

open scoped TensorProduct

variable {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]

def phi (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) : K ⊗[F] E →ₐ[K] K × K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (ι.prod (ι.comp σ)) (fun _ _ => Commute.all _ _)

theorem phi_tmul (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (x : K) (e : E) :
    phi σ ι (x ⊗ₜ[F] e) = (x * ι e, x * ι (σ e)) := by
  simp [phi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Prod.algebraMap_apply]

theorem phi_bijective (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (h2 : Module.finrank F E = 2) (a : E) (ha : σ a ≠ a) :
    Function.Bijective (phi σ ι) := by
  have hne : ι a - ι (σ a) ≠ 0 := by
    intro h
    exact ha (ι.injective (sub_eq_zero.mp h)).symm
  have hsurj : Function.Surjective (phi σ ι) := by
    rintro ⟨u, v⟩
    refine ⟨((u - v) / (ι a - ι (σ a))) ⊗ₜ[F] a + (u - (u - v) / (ι a - ι (σ a)) * ι a) ⊗ₜ[F] (1 : E), ?_⟩
    rw [map_add (f := _), phi_tmul, phi_tmul]
    simp only [map_one, mul_one, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · ring
    · field_simp
      ring
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hr : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2, Module.finrank_prod, Module.finrank_self]
  have key := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr
    (f := (phi σ ι).toLinearMap)).mpr (by exact hsurj)
  exact ⟨by exact key, hsurj⟩

theorem phi_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (ι : E →ₐ[F] K) (t : K ⊗[F] E) :
    phi σ ι (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ t) = (phi σ ι t).swap := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, hσ, Prod.swap_prod_mk]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    rfl

end MassDataIdxSplit

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def EmbP {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nonempty (X.B.I.E →ₐ[X.B.I.F] FpX X p)

theorem splitTheta_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : EmbP X p) :
    ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ := by
  obtain ⟨ι⟩ := h
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hex : ∃ a, X.B.I.cm.sig a ≠ a := by
    by_contra hne
    push_neg at hne
    have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr ?_
      obtain ⟨y, hy⟩ := (X.B.I.cm.fixed x).1 (hne x)
      exact ⟨y, hy⟩
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    omega
  obtain ⟨a, ha⟩ := hex
  exact ⟨AlgEquiv.ofBijective (MassDataIdxSplit.phi X.B.I.cm.sig ι)
    (MassDataIdxSplit.phi_bijective _ ι h2 a ha), fun t => MassDataIdxSplit.phi_sig _ hσ ι t⟩

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffSG
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

theorem reindex_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι) (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

private theorem flagC_reindex_iff {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Fin n ≃ ι) (M : Matrix (Fin n) (Fin n) K) (v : Fin m → Fin n → K) :
    FlagC (Matrix.reindex e e M) (fun b => v b ∘ e.symm) ↔ FlagC M v := by
  let f : (Fin n → K) ≃ₗ[K] (ι → K) := LinearEquiv.funCongrLeft K K e.symm
  have hmv : ∀ w : Fin n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm := by
    intro w
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    ext i
    simp [Function.comp_def]
  have key : ∀ (x : Fin n → K) (S : Set (Fin n → K)),
      x ∘ e.symm ∈ Submodule.span K ((fun w : Fin n → K => w ∘ e.symm) '' S) ↔ x ∈ Submodule.span K S := by
    intro x S
    have h1 : (fun w : Fin n → K => w ∘ e.symm) = ⇑(f.toLinearMap) := rfl
    rw [h1, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := f.injective hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold FlagC
  refine forall_congr' fun b => ?_
  show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈
      Submodule.span K ((fun a => v a ∘ e.symm) '' {a | a < b}) ↔ _
  rw [hmv, show (fun a => v a ∘ e.symm) '' {a | a < b} =
      (fun w : Fin n → K => w ∘ e.symm) '' (v '' {a | a < b}) from
      (Set.image_image (fun w : Fin n → K => w ∘ e.symm) v {a | a < b}).symm]
  exact key (M *ᵥ v b - v b) _

theorem mem_Ssub_iff_sG (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) {r k : ℕ} (e : Fin n ≃ Idx r k)
    (hJ : IsUnit (jm1 J θ).det) (P : Frame E n r) (Q : GL (Idx r k) R) (l : Fin (r + 1) → R)
    (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) *ᵥ
      (pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) R)ᵀ *ᵥ ((Matrix.reindex e e (jm1 J θ))ᵀ *ᵥ
      (pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)) = l b • Pi.single (pf b) 1)
    (g : HA R σ J) (g1 : GL (Idx r k) R)
    (hg1 : (g1 : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (cmp1 σ J θ g)) :
    g ∈ Ssub R σ J P ↔ Q⁻¹ * g1 * Q ∈ sG R r k := by
  rw [mem_Ssub_iff_flagC σ J θ P g]
  have hU : (Matrix.reindex e e (cmp2 σ J θ g))ᵀ * Matrix.reindex e e (jm1 J θ) *
      ((g1 : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (jm1 J θ) := by
    rw [hg1, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit σ J θ hθ g]
  have hJ' : IsUnit (Matrix.reindex e e (jm1 J θ)).det := by
    rwa [Matrix.det_reindex_self]
  rw [← frame_mem_sG g1 Q _ _ hJ' hU (fun b => pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)
    (fun b => pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) l hl hy1 hy2, hg1]
  exact and_congr (flagC_reindex_iff e _ _).symm (flagC_reindex_iff e _ _).symm

end MassDataIdxStIm
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxStImB MassDataIdxRed

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev SuX (u : D.what₂.Word) (p : TypX X) : Subgroup (HAp X p) :=
  Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)

def StSImgB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ((SuX X u p).comap K.subtype).map ψ = (sG (Op X p) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem parabolic_image_of_residue (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (hS : StSImgB X u p) :
    ParabolicReductionImage X u p := by
  obtain ⟨π, hπ, hker⟩ := hR
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := hS
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) := (glRed π).comp ψ with hρ₀
  have hker₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hmemK : ∀ y : HAp X p, y ∈ KvX X p → y ∈ K := fun y hy => by
    rw [← SetLike.mem_coe, hK]; exact hy
  refine ⟨K, hK, ρ₀, (glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ, hker₀,
    (SuX X u p).comap K.subtype ⊔ ρ₀.ker, ?_, le_sup_right, glRed π c, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, κ, hκ, rfl⟩ := (mem_sup_ker ρ₀ _).1 hx
      have hκ' : (κ : HAp X p) ∈ KgX X p := (hker₀ κ).1 hκ
      have hsK : (s : HAp X p) ∈ KvX X p := by rw [← hK]; exact s.2
      have hxK : ((s * κ : K) : HAp X p) ∈ KvX X p := by rw [← hK]; exact (s * κ).2
      exact ⟨hxK, s, κ, hs, hsK, hκ', rfl⟩
    · rintro ⟨hy, s, κ, hs, hsK, hκ, rfl⟩
      refine ⟨⟨s, hmemK s hsK⟩ * ⟨κ, hmemK κ hκ.1⟩, ?_, rfl⟩
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact hs
      · rw [MonoidHom.mem_ker, hker₀]; exact hκ
  · rw [map_sup_ker, hρ₀, ← Subgroup.map_map, hc, map_conj,
      sG_map_glRed π hπ]

def StFrameB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, (x : HAp X p) ∈ SuX X u p ↔ c⁻¹ * ψ x * c ∈ sG (Op X p) D.R.rS D.R.k

theorem stSImgB_of (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : StSImgB X u p := by
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := h
  exact ⟨K, hK, ψ, hψ, hP, c, map_eq_conj ψ hψ _ _ c fun x => hc x⟩

theorem parabolic_image_of_residue_frame (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (h : StFrameB X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_residue X u p hR (stSImgB_of X u p h)

theorem parabolic_image_of_frame (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : ParabolicReductionImage X u p :=
  parabolic_image_of_residue_frame X u p (stResZ_holds X p) h

end Loc

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReindexGl
noncomputable section

namespace MassDataIdxCore

open Matrix

theorem reindex_gl {H R : Type} [Group H] [CommRing R] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ≃ ι) (I : Ideal R) (Q : H → Prop) (ψ : H →* GL n R) (hψ : Function.Surjective ψ)
    (hQ : ∀ h, (∀ i j, (((ψ h : GL n R) : Matrix n n R) - 1) i j ∈ I) ↔ Q h) :
    ∃ ψ' : H →* GL ι R, Function.Surjective ψ' ∧
      ∀ h, (∀ i j, (((ψ' h : GL ι R) : Matrix ι ι R) - 1) i j ∈ I) ↔ Q h := by
  classical
  let φ : GL n R ≃* GL ι R := Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv
  refine ⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψ, fun h => ?_⟩
  rw [← hQ h]
  have key : ∀ i j, (((φ.toMonoidHom.comp ψ h : GL ι R) : Matrix ι ι R) - 1) i j =
      (((ψ h : GL n R) : Matrix n n R) - 1) (e.symm i) (e.symm j) := by
    intro i j
    simp [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  simp only [key]
  constructor
  · intro H i j
    simpa using H (e i) (e j)
  · intro H i j
    exact H _ _

end MassDataIdxCore
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def CoreAll : Prop :=
  ∀ (K T : Type) [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) (n : Type) [Fintype n]
    [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K),
    (∀ t, θ (s t) = (θ t).swap) → Formalism.UG.cT s J = J → IsUnit J.det →
    MassDataIdxCore.KerBack O θ s J P ∧ MassDataIdxCore.SurjCore O θ s J P

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem herm_JR : Formalism.UG.cT (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) = JR (FpX X p) X.B.I.J := by
  have hJ := X.B.I.J_herm
  unfold Formalism.UG.IsHerm at hJ
  ext i j
  have h1 := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
  simp only [JR, Matrix.map_apply, sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← h1]
  rfl

theorem unit_JR : IsUnit (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det := by
  have h1 : (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det = inclR (F := X.B.I.F) (FpX X p) X.B.I.J.det := by
    unfold JR
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr X.B.I.J_det).map _

end Loc

theorem latCore_of (hC : CoreAll) : LatCore := by
  intro D X p θ hθ P hP K hK
  obtain ⟨hKB, hSU⟩ := hC (FpX X p) (TpX X p) (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hθ (herm_JR X p) (unit_JR X p)
  have hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := hP
  let m : K →* GL (Fin X.B.I.n) (TpX X p) :=
    (HR (FpX X p) X.B.I.cm.sig X.B.I.J).subtype.comp K.subtype
  have hmem : ∀ h : K, HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J (h : HAp X p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro h
    have : (h : HAp X p) ∈ (K : Set (HAp X p)) := h.2
    rw [hK] at this
    exact this
  have hKl : ∀ h x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
      ((m h : GL (Fin X.B.I.n) (TpX X p)) : Matrix _ _ (TpX X p)) *ᵥ x ∈
        MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := by
    intro h x
    rw [← hLat, ← hLat]
    exact hmem h x
  have hon : ∀ g : GL (Fin X.B.I.n) (TpX X p), g ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) →
      (∀ x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
        (g : Matrix _ _ (TpX X p)) *ᵥ x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ
          (JR (FpX X p) X.B.I.J) P) → ∃ h, m h = g := by
    intro g hg hgs
    let x0 : HAp X p := ⟨g, hg⟩
    have hin : x0 ∈ K := by
      rw [← SetLike.mem_coe, hK]
      show g ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
      intro x
      rw [hLat, hLat]
      exact hgs x
    exact ⟨⟨_, hin⟩, rfl⟩
  obtain ⟨ψ, hψ, hker⟩ := MassDataIdxCore.latGL_gen (p.1.adicCompletionIntegers X.B.I.F) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hKB hSU ((gOf p : ℕ) : Op X p) m (fun h => (h : HAp X p).2)
    hKl hon
  refine MassDataIdxCore.reindex_gl (idxEquiv X) _ _ ψ hψ (fun h => ?_)
  rw [hker h]
  have hsm : ∀ z : Fin X.B.I.n → TpX X p,
      (((gOf p : ℕ) : Op X p) : FpX X p) • z = ((gOf p : ℕ) : Op X p) • z := fun z => rfl
  constructor
  · intro H0
    refine ⟨(hmem h), fun y hy => ?_⟩
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).1 hy)
    exact ⟨z, (hLat z).2 hz, by rw [← hsm]; exact hz'⟩
  · rintro ⟨-, H0⟩ y hy
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).2 hy)
    exact ⟨z, (hLat z).1 hz, by rw [hsm]; exact hz'⟩

theorem stRed_of_core {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : CoreAll) : StRed X p := stRed_of_parts X p hR hS (latCore_of hC)

end MassDataIdxSteps
end
end

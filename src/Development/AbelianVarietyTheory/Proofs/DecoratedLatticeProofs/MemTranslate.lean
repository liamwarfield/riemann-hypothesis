module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem rTrans_rTrans {G : Type} [Semigroup G] (a b : G) (F : G → ℂ) : rTrans a (rTrans b F) = rTrans (a * b) F := by
  funext g; simp [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans 1 F = F := by
  funext g; simp [rTrans]

def space (Q : QStep S) : Submodule ℂ (GA D S.B'.V → ℂ) where
  carrier := {f | (∀ y, IsContAut S.B'.V (rTrans (Q.gl₂ y) f)) ∧
    ∃ U : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), IsOpen (U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)) ∧
      ∀ u ∈ U, rTrans (Q.gl₂ u) f = f}
  zero_mem' := ⟨fun y => ⟨fun _ _ _ => rfl, continuous_const⟩, ⊤, isOpen_univ, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, U, hU, hfU⟩ ⟨hg, V, hV, hgV⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U ⊓ V, hU.inter hV, fun u hu => ?_⟩
    · change f (γ * x * _) + g (γ * x * _) = f (x * _) + g (x * _)
      have h1 := (hf y).1 γ hγ x
      have h2 := (hg y).1 γ hγ x
      simp only [rTrans] at h1 h2
      rw [h1, h2]
    · exact (hf y).2.add (hg y).2
    · have h1 := hfU u hu.1
      have h2 := hgV u hu.2
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [rTrans, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  smul_mem' := by
    rintro a f ⟨hf, U, hU, hfU⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U, hU, fun u hu => ?_⟩
    · have h1 := (hf y).1 γ hγ x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
    · exact continuous_const.mul (hf y).2
    · have h1 := hfU u hu
      funext x
      have e1 := congrFun h1 x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]

theorem mem_translate (Q : QStep S) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) {f : GA D S.B'.V → ℂ} (hf : f ∈ space Q) :
    rTrans (Q.gl₂ y) f ∈ space Q := by
  obtain ⟨hc, U, hU, hfU⟩ := hf
  refine ⟨fun y' => ?_, U.comap (MulAut.conj y⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
  · rw [rTrans_rTrans, ← map_mul]; exact hc _
  · have hc : Continuous fun x : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k => y⁻¹ * x * y⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · have hu' : y⁻¹ * u * y ∈ U := by simpa using hu
    rw [rTrans_rTrans, ← map_mul, show u * y = y * (y⁻¹ * u * y) by group, map_mul, ← rTrans_rTrans, hfU _ hu']

def rep (Q : QStep S) : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) (space Q) where
  toFun y :=
    { toFun := fun f => ⟨rTrans (Q.gl₂ y) f.1, mem_translate Q y f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp [rTrans]
  map_mul' x y := by
    ext f g
    rw [Module.End.mul_apply]
    change f.1 (g * Q.gl₂ (x * y)) = f.1 (g * Q.gl₂ x * Q.gl₂ y)
    rw [map_mul, mul_assoc]

def valK (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ)
    (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ))
    (Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k)) (f : GA D S.B'.V → ℂ) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) f

theorem smooth (Q : QStep S) : IsSmoothRep (rep Q) := by
  intro v
  obtain ⟨-, U, hU, hfU⟩ := v.2
  let H : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) :=
    { carrier := {g | rep Q g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : U ≤ H := fun u hu => Subtype.ext (hfU u hu)
  exact Subgroup.isOpen_mono hle hU

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramePeriod

variable {D : D7}

theorem setIntegral_mul_right_N {ρ : ℕ} (B : BesLev D ρ) (G : flagN B.d → ℂ)
    (hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n, G (γ * n) = G n) (y : flagN B.d) :
    ∫ n in B.vN.𝓝, G (n * y) ∂B.vN.ν = ∫ n in B.vN.𝓝, G n ∂B.vN.ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  haveI : DiscreteTopology (NFlagQ B.V B.d.e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B.V B.d.e => (⟨γ.1.1, γ.2⟩ : GQ B.V)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B.V => (x : GA D B.V)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  have hcov' : ∀ x : flagN B.d, ∃ s ∈ NFlagQ B.V B.d.e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : flagN B.d, B.vN.ν.map (· * a) = B.vN.ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vN.ν (NFlagQ B.V B.d.e) hK hcov' a
  have hmp : MeasurePreserving (· * y) B.vN.ν B.vN.ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) B.vN.ν B.vN.ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) G B.vN.𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B.V B.d.e) ((· * y⁻¹) ⁻¹' B.vN.𝓝) B.vN.ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem inner_N {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n ∂B.vN.ν =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨-, -, hconj, -, -⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hx' : GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹ ∈ flagN B.d := hconj x hx h
  have hpy : psiBes ψ B.d 1 (vecB B.o B.ζ) (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x := hψconj x h
  have hn1 : psiBes ψ B.d 1 (vecB B.o B.ζ) x * star (psiBes ψ B.d 1 (vecB B.o B.ζ) x) = 1 := by
    have hnorm : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) x‖ = 1 := by simp only [psiBes, psiE]; exact hψ.2.1 _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  let y : flagN B.d := ⟨_, hx'⟩
  have hpt : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * besFun ψ 1 B.d B.o B.ζ φ f h (n * y) := fun n => by
    simp only [besFun, rTrans, Subgroup.coe_mul, y]
    rw [psiBes_mul B.d ψ 1 _ n.2 hx', hpy, star_mul]
    have e1 : (n : GA D B.V) * (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) *
        GlobalTheory.MixPer.embA B.d B.o h = (n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x := by group
    rw [e1]
    linear_combination (-(φ h * f ((n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x) *
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n : GA D B.V)))) * hn1
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_mul_right_N B _ hG y]

theorem per_flagN {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) :
    B.per ψ φ (rTrans x f) = psiBes ψ B.d 1 (vecB B.o B.ζ) x * B.per ψ φ f := by
  unfold BesLev.per besPer
  simp_rw [inner_N B ψ hψ.1 φ f hf hx]
  exact integral_const_mul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_embA (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {g : GL n k}
    {h : GA D B.A} (hh : p.IsLoc FA h g) : p.IsLoc F (GlobalTheory.MixPer.embA B.d B.o h) (embX c g) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [GlobalTheory.MixPer.embA_apply]
  refine ⟨GlobalTheory.LocGrp.suppAt_wittLeviEmbedding B.d (GlobalTheory.LocGrp.suppAt_emb B.o hh.1),
    GlobalTheory.LocGrp.eq_embX F _ g ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (GlobalTheory.LocGrp.intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r =>
      (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩
      (hY _ j (by simp only; omega))

end GlobalTheory.NormalFramePeriod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EntrySB
open scoped Pointwise

theorem exists_nhds_add_eq {M E : Type*} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Zero E]
    {F : M → E} (hl : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ V ∈ nhds (0 : M), ∀ x, ∀ v ∈ V, F (x + v) = F x := by
  letI : TopologicalSpace E := ⊥
  haveI : DiscreteTopology E := ⟨rfl⟩
  have hT : (F '' tsupport F).Finite := (hc.isCompact.image hl.continuous).finite_of_discrete
  have hsep : ∀ a : E, ∃ W ∈ nhds (0 : M), a ≠ 0 → F ⁻¹' {a} + W ⊆ F ⁻¹' {a} := by
    intro a
    by_cases ha : a = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h ha).elim⟩
    · have hsub : F ⁻¹' {a} ⊆ tsupport F := fun y hy =>
        subset_tsupport F (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy; simp [Function.mem_support, hy, ha])
      have hK : IsCompact (F ⁻¹' {a}) := hc.isCompact.of_isClosed_subset (hl.isClopen_fiber a).isClosed hsub
      obtain ⟨W, hW, hW'⟩ := compact_open_separated_add_right hK (hl.isOpen_fiber a) le_rfl
      exact ⟨W, hW, fun _ => hW'⟩
  choose W hW hWs using hsep
  refine ⟨⋂ a ∈ F '' tsupport F, (W a ∩ -W a), (Filter.biInter_mem hT).2 fun a _ =>
    Filter.inter_mem (hW a) (neg_mem_nhds_zero M (hW a)), ?_⟩
  intro x v hv
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_neg] at hv
  by_cases hx : F x = 0
  · by_contra hne
    have hxv : x + v ∈ tsupport F := subset_tsupport F (by rw [Function.mem_support]; rwa [hx] at hne)
    have hb : F (x + v) ≠ 0 := fun h => hne (h.trans hx.symm)
    have := hWs (F (x + v)) hb (Set.add_mem_add (a := x + v) (b := -v) rfl (hv _ ⟨_, hxv, rfl⟩).2)
    simp only [add_neg_cancel_right, Set.mem_preimage, Set.mem_singleton_iff] at this
    exact hne this.symm
  · have hxs : x ∈ tsupport F := subset_tsupport F hx
    have := hWs (F x) hx (Set.add_mem_add (a := x) (b := v) rfl (hv _ ⟨_, hxs, rfl⟩).1)
    simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Aff
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem affPt_add (p : ℕ) (x₀ v : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p (x₀ + v) e = affPt p x₀ e + fromBlocks v 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> simp [affPt, basePt] <;> ring

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem ch_fromBlocks (v : Matrix n n' k) :
    ch (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) = 0 := by
  simp [ch]

theorem corner_affPt (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    (Matrix.of fun i j => affPt p x₀ e (Sum.inl i) (Sum.inl j)) = x₀ := by
  ext i j
  simp [affPt, basePt, Free]

variable [MeasurableSpace k] [BorelSpace k]

theorem opE_mem_SB (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hF : F ∈ SB _) :
    GlobalTheory.RootEx.opE ψ ν p F ∈ SB (Matrix n n' k) := by
  obtain ⟨hl, hc⟩ := hF
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hVF⟩ := exists_nhds_add_eq hl hc
    have hι : Continuous fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
      continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
    have hW : (fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ⁻¹' V ∈ nhds (0 : Matrix n n' k) := by
      apply hι.continuousAt.preimage_mem_nhds
      simpa [fromBlocks_zero] using hV
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
    rw [← map_add_left_nhds_zero x₀, Filter.eventually_map]
    filter_upwards [hW] with v hv
    simp only [GlobalTheory.RootEx.opE]
    congr 1
    funext e
    rw [affPt_add, hVF _ _ hv, ch_add, ch_fromBlocks, add_zero]
  · have hpr : Continuous fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        (Matrix.of fun i j => M (Sum.inl i) (Sum.inl j) : Matrix n n' k) :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    refine HasCompactSupport.intro (hc.isCompact.image hpr) fun x₀ hx₀ => ?_
    have h0 : ∀ e, F (affPt p x₀ e) = 0 := fun e => image_eq_zero_of_notMem_tsupport fun hm =>
      hx₀ ⟨_, hm, corner_affPt p x₀ e⟩
    simp [GlobalTheory.RootEx.opE, h0]

end Aff

end GlobalTheory.EntrySB


open GlobalTheory.EntrySB in
theorem GlobalTheory.StepData.xi_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ _ ν _ μ Φ J b h' h
  have := Submodule.smul_mem (SB (Matrix n n' k)) ((((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ))
    (opE_mem_SB ψ ν 1 (GlobalTheory.SplitWeil.om_mem_SB μ h' h Φ.2))
  convert this using 1
  funext x
  simp [xi, flat]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_entries_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.StepData.xi_mem_SB | exact GlobalTheory.StepData.xi_mem_SB | (intros; apply GlobalTheory.StepData.xi_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_box {n : Type} [Fintype n] {M : Matrix n n k} (hM : IntM M) {c : kˣ} {y : n → k}
    (hy : y ∈ box n c) : M *ᵥ y ∈ box n c := by
  rw [mem_box] at hy ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hM i j) (hy j)

theorem toBlocks₁₁_mul {n : Type} [Fintype n] (M N : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j; simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Fintype.sum_sum_type]

theorem toBlocks₁₁_one {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem withCol_mul {n n' : Type} [Fintype n] (κ : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (x₀ : Matrix n n' k)
    (y : n → k) : κ * withCol x₀ y = withCol (κ.toBlocks₁₁ * x₀) (κ.toBlocks₁₁ *ᵥ y) := by
  ext (r | r) (c | c)
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct]
  · exact r.elim0
  · exact r.elim0

theorem box_eq_preimage {n : Type} (c : kˣ) :
    (box n c : Set (n → k)) = (fun y : n → k => ((c⁻¹ : kˣ) : k) • y) ⁻¹' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
  ext y
  simp only [SetLike.mem_coe, mem_box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_box {n : Type} [Fintype n] (c : kˣ) : IsOpen (box n c : Set (n → k)) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => (valuation k).isOpen_integer).preimage (continuous_const_smul _)

theorem isCompact_box {n : Type} [Fintype n] (c : kˣ) : IsCompact (box n c : Set (n → k)) := by
  have hK : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have e : (box n c : Set (n → k)) = (fun y : n → k => (c : k) • y) '' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    rw [box_eq_preimage, Set.image_eq_preimage_of_inverse]
    · intro y; simp [smul_smul]
    · intro y; simp [smul_smul]
  rw [e]
  exact (isCompact_univ_pi fun _ => hK).image (continuous_const_smul _)

theorem finite_image_box {n : Type} [Fintype n] (c₁ c₂ : kˣ) :
    ((Submodule.Quotient.mk (p := box n c₂)) '' (box n c₁ : Set (n → k))).Finite := by
  obtain ⟨t, -, ht⟩ := (isCompact_box (n := n) c₁).elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' (box n c₂ : Set (n → k)))
    (fun y _ => ((isOpen_box c₂).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by show y - y ∈ box n c₂; rw [sub_self]; exact zero_mem _))
  refine (t.finite_toSet.image (Submodule.Quotient.mk (p := box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨z, hz, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← neg_sub]; exact neg_mem hyz

theorem om_one_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) (hx : om μ 1 h Φ x ≠ 0) : Φ ((h⁻¹ : GL b k).val * x) ≠ 0 := by
  unfold om at hx
  have := right_ne_zero_of_mul hx
  simpa using this

theorem om_g_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (Φ : Matrix b a k → ℂ) (x x' : Matrix b a k) (hx : om μ g 1 Φ x ≠ 0)
    (h : Φ (x * g.val) ≠ 0 → Φ (x' * g.val) ≠ 0) : om μ g 1 Φ x' ≠ 0 := by
  unfold om at *
  simp only [inv_one, Units.val_one, Matrix.one_mul] at *
  exact mul_ne_zero (left_ne_zero_of_mul hx) (h (right_ne_zero_of_mul hx))

end GlobalTheory.QPl.CoupStab

namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem psi_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hL : T.Laws) {κ : GL (X (s + 1) ⊕ Fin 0) k} (hκ : κ ∈ (T.lev (s + 1) 0 rfl).J)
    (g : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (h : T.Psi g x₀ y ≠ 0) :
    T.Psi g (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) ≠ 0 := by
  have hPhi : ∀ x, T.Phi s 0 rfl x ≠ 0 → T.Phi s 0 rfl (κ.val * x) ≠ 0 := by
    intro x hx
    have e := congrFun ((hL.1 s 0 rfl).2 ⟨κ⁻¹, inv_mem hκ⟩) x
    have hr : om (T.mu (s + 1)) 1 (κ⁻¹ : GL (X (s + 1) ⊕ Fin 0) k) (T.Phi s 0 rfl) x ≠ 0 := by
      rw [e, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Units.ne_zero _) hx
    simpa using om_one_ne _ _ _ _ hr
  unfold Chain.Psi at *
  refine om_g_ne _ _ _ _ _ h fun h' => ?_
  rw [← withCol_mul, Matrix.mul_assoc]
  exact hPhi _ h'

theorem coupIdx_stab : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  intro D c v χ Q
  have hB : ∀ {g : GL (Q.X (Q.s + 1) ⊕ Fin 0) Q.k}, g ∈ (Q.T.lev (Q.s + 1) 0 rfl).J → IntM g.val.toBlocks₁₁ :=
    fun hg i j => intM_of_mem_KO (Q.le _ _ _ hg) (.inl i) (.inl j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (finite_image_box Q.c₁ Q.c₂).subset (by rintro _ ⟨y, hy, rfl, -⟩; exact ⟨y, hy, rfl⟩)
  · intro yb
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    refine ⟨1, one_mem _, y, rfl, ?_⟩
    rw [Units.val_one, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, _, rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, ← toBlocks₁₁_mul, Units.inv_mul, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ _ ⟨g, hg, y, rfl, h1⟩ ⟨g', hg', y', h2, h3⟩
    refine ⟨g' * g, mul_mem hg' hg, y, rfl, ?_⟩
    rw [← h3, Units.val_mul, toBlocks₁₁_mul, ← Matrix.mulVec_mulVec]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Matrix.mulVec_sub]
    exact mulVec_mem_box (hB hg') ((Submodule.Quotient.eq _).1 (h1.trans h2.symm))
  · rintro _ ⟨y₁, -, rfl, g, hg, x₀, hΨ⟩ _ ⟨κ, hκ, y, hy, rfl⟩
    have hd : y - y₁ ∈ box _ Q.c₂ := (Submodule.Quotient.eq _).1 hy
    have hΨy : Q.T.Psi g x₀ y ≠ 0 := by
      rw [show y = y₁ + (y - y₁) by abel, (Q.adapt g hg x₀ y₁).2 _ hd]; exact hΨ
    exact ⟨_, mulVec_mem_box (hB hκ) ((Q.adapt g hg x₀ y).1 hΨy), rfl, g, hg, _,
      psi_ne Q.T Q.laws hκ g x₀ y hΨy⟩

end GlobalTheory.QPl.CoupStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  first | exact @GlobalTheory.QPl.CoupStab.coupIdx_stab | exact GlobalTheory.QPl.CoupStab.coupIdx_stab | (intros; apply GlobalTheory.QPl.CoupStab.coupIdx_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalDoublingIntegralOddCase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.ContrSum

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_colE_indep {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ)
    (μ : kˣ →* ℂˣ) (β : n → k) (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    om μ 1 (colE c p β) Φ = om 1 1 (colE c p β) Φ := by
  have h : Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
    apply Units.ext
    simp [colE, upU, Matrix.GeneralLinearGroup.val_det_apply]
  funext x
  simp only [om, h, map_one]

theorem isClosedEmbedding_negCol (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n → k) =>
      (fromCols q.1 (Matrix.of fun r (_ : Unit) => (-q.2) r) : Matrix n (n' ⊕ Unit) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix n (n' ⊕ Unit) k => (z.toCols₁, fun r => -z r (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, β⟩
    simp
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun r => (continuous_id.matrix_elem _ _).neg)
  · refine continuous_matrix fun r s => ?_
    rcases s with s | s
    · exact continuous_fst.matrix_elem _ _
    · exact ((continuous_apply r).comp continuous_snd).neg

theorem isClosedEmbedding_row (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n' → k) =>
      (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2) : Matrix (n ⊕ Unit) n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix (n ⊕ Unit) n' k => (z.toRows₁, z (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, u⟩
    rfl
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun s => continuous_id.matrix_elem _ _)
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r
    · exact continuous_fst.matrix_elem _ _
    · exact (continuous_apply s).comp continuous_snd

theorem exists_sum_prod (n n' m' : Type) [Fintype n] [Fintype n'] [Fintype m']
    (F : SB (Matrix n n' k × (m' → k))) :
    ∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n n' k)) (Φ₀ : Fin m → SB (m' → k)),
      ∀ x β, F.1 (x, β) = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix n n' k) := inferInstanceAs (TotallyDisconnectedSpace (n → n' → k))
  haveI : LocallyCompactSpace (Matrix n n' k) := inferInstanceAs (LocallyCompactSpace (n → n' → k))
  haveI : T2Space (Matrix n n' k) := inferInstanceAs (T2Space (n → n' → k))
  have hmem : F ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix n n' k) × SB (m' → k) => prodSB q.1 q.2) := by
    rw [Span.span_prodSB_eq_top]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  refine ⟨N, fun i => f i • (p i).1, fun i => (p i).2, fun x β => ?_⟩
  rw [← hq, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hp i]
  simp only [prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

variable [MeasurableSpace k] [BorelSpace k]

theorem fl_eq_flCol (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν)
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (h1 : 1 ≤ ρ) (hc : c = 2 * ρ)
    (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n n' k) (β : n → k) :
    fl ψ ν μ ρ Φ.1 x β = flCol ψ ν (ρ + 1) Φ.1 (fromCols x (Matrix.of fun r (_ : Unit) => (-β) r)) := by
  have h := (((GlobalTheory.RootEx.FourierJacobi.fourierJacobiBessel k).2.2.2.1 n n' c ρ h1 hc).2.2.2 ψ ν hψ hne hν).1
    1 continuous_const Φ β
  have h2 := h.2 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.fl at h2 ⊢
  rw [om_colE_indep, h2]
  rfl

theorem contr_flat_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ : kˣ →* ℂˣ) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1 ∈ SB (Matrix n₁ (n₀ ⊕ Unit) k) ∧ GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1 ∈ SB (Matrix (n₂ ⊕ Unit) n₁ k) ∧ (∀ Φ₀ : SB (n₁ → k), opEFJ ψ ν ρ Φ₀.1 Φ₂.1 ∈ SB (Matrix n₂ n₁ k)) ∧ (∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), ∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) ∧ ∀ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), (∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) → ∀ x, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1) x = ∑ i, (Ψ i).1 x.1 * opEFJ ψ ν ρ (Φ₀ i).1 Φ₂.1 x.2 := by
  intro k _ _ _ _ _ _ ψ hψ hne ν hν n₀ _ _ n₁ _ _ n₂ _ _ c ρ hc μ Φ₁ Φ₂
  haveI := hν.1
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix n₂ n₁ k) := inferInstanceAs (T2Space (n₂ → n₁ → k))
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular ν
  have h1 : 1 ≤ ρ := by omega
  have hA := ((flat_SB_onto k ψ ν hψ hν.1 n₁ n₀ (c + 1) (ρ + 1) (by omega)).1 (by omega)).1 _ Φ₁.2
  have hB := ((flat_SB_onto k ψ ν hψ hν.1 n₂ n₁ c ρ h1).2 (by omega)).1 _ Φ₂.2
  have hfl := fl_eq_flCol ψ hψ hne ν hν (c + 1) ρ h1 hc μ Φ₁
  have hG : (fun q : Matrix n₂ n₁ k × (n₁ → k) =>
      flRow ψ ν ρ Φ₂.1 (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2))) ∈ SB _ :=
    ⟨hB.1.comp_continuous (isClosedEmbedding_row n₂ n₁).continuous,
      hB.2.comp_isClosedEmbedding (isClosedEmbedding_row n₂ n₁)⟩
  have hE : ∀ (Φ₀ : (n₁ → k) → ℂ) (x : Matrix n₂ n₁ k), opEFJ ψ ν ρ Φ₀ Φ₂.1 x =
      ∫ u, flRow ψ ν ρ Φ₂.1 (fromRows x (Matrix.of fun (_ : Unit) => u)) * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀ u
        ∂(Measure.pi fun _ => ν) := by
    intro Φ₀ x
    unfold opEFJ
    congr 1
    funext u
    rw [mul_comm]
    rfl
  refine ⟨hA, hB, fun Φ₀ => ?_, ?_, fun m Ψ Φ₀ hd x => ?_⟩
  · rw [funext (hE Φ₀.1)]
    exact integral_mul_mem_SB _ _ hG _
  · obtain ⟨m, Ψ, Φ₀, h⟩ := exists_sum_prod n₁ n₀ n₁
      ⟨_, hA.1.comp_continuous (isClosedEmbedding_negCol n₁ n₀).continuous,
        hA.2.comp_isClosedEmbedding (isClosedEmbedding_negCol n₁ n₀)⟩
    exact ⟨m, Ψ, Φ₀, fun x β => (hfl x β).trans (h x β)⟩
  · obtain ⟨c₀, hc₀⟩ := (conductor_exists k).1 ψ hψ hne
    have hhat : ∀ u, GlobalTheory.StepData.hat ψ ν (-1)
        (fun y => flCol ψ ν (ρ + 1) Φ₁.1 (fromCols x.1 (Matrix.of fun r (_ : Unit) => y r))) u =
        ∑ i, (Ψ i).1 x.1 * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u := by
      intro u
      unfold GlobalTheory.StepData.hat GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat
      rw [← integral_neg_eq_self]
      simp only [← hfl, hd, dotProduct_neg, neg_mul_neg, one_mul, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro i _
        have := GlobalTheory.StepData.integrable_hat ψ ν 1 hψ (Φ₀ i).2 u
        simp only [one_mul] at this
        exact this.const_mul _
    unfold contr
    simp only [hhat, hE, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    · intro i _
      have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n₁ => ν) hc₀ (Φ₀ i).2
      have hF' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 ∈ SB (n₁ → k) := by
        convert hF using 1
        funext y
        simp [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm]
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hF'.2.mul_left)
      exact (hG.1.continuous.comp (Continuous.prodMk_right x.2)).mul (continuous_const.mul hF'.1.continuous)

end GlobalTheory.LocFlat.ContrSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardOrderSymmInr
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymChain.NonZeroAt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Coords
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change (fromBlocks 1 0 0 (diagonal _) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · simp
  · simp [mul_inv_cancel₀, pow_ne_zero]

end Coords

section Ord
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ord

section Chain
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]


end Chain

section Entry
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Entry

section Main
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Main

section Final
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Final

end GlobalTheory.SymChain.NonZeroAt

namespace GlobalTheory.SymChain

end GlobalTheory.SymChain
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NChainChar

theorem edge_sum_typeFrame {K : Type} [Field K] (κ τ s N r p : ℕ) (hr : r ≤ N) (hrk : r = κ + (s + 1))
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) 0 ≃ Fin N) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (ϖ : Kˣ)
    (q : GL (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) K) (hq : GlobalTheory.RootEx.InN p q) :
    (∑ i : Fin r, ∑ j : Fin r, if GlobalTheory.chainEdge κ i j then
      (((GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas⁻¹).val * q.val *
        (GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas.val)
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (ϖ : K) * GlobalTheory.RootEx.simpleSum q := by
  subst hrk
  rw [GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_inv_val, GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  let ε : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have hε : ∀ a, e.symm (Fin.castLE hr (ε a)) = Sum.inl a := by
    intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [he]
    rcases a with a | a <;> simp [ε, GlobalTheory.SymBridge.zPos]
  rw [← ε.sum_comp]
  simp only [← ε.sum_comp (fun j => ite _ _ _), hε]
  have h1 : ∀ i : Fin κ, GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl (Sum.inl i)) := fun i => rfl
  have h2 : ∀ i : Fin (s + 1), GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inr i)) =
      Sum.inr i := fun i => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) i
  have hX : ∀ a b : GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0,
      q.val (Sum.inl a) (Sum.inl b) = (1 : Matrix (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) _ K) (Sum.inl a) (Sum.inl b) :=
    fun a b => hq _ _ le_rfl
  have eε1 : ∀ i : Fin κ, (ε (Sum.inl i)).val = i.val := fun i => rfl
  have eε2 : ∀ i : Fin (s + 1), (ε (Sum.inr i)).val = κ + i.val := fun i => rfl
  simp only [Fintype.sum_sum_type, h1, h2, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, GlobalTheory.chainEdge, eε1, eε2]
  have A : ∀ x : Fin κ, ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = 0 := by
    intro x
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro x_1 _
      rw [if_neg]
      omega
    · intro x_1 _
      split_ifs with h
      · rw [hX, Matrix.one_apply_ne]
        intro e
        have : x = x_1 := by simpa using e
        subst this
        omega
      · rfl
  have B : ∀ x : Fin (s + 1), ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = (ϖ : K) * ∑ x_1 : Fin (s + 1), if (x_1 : ℕ) = x + 1 then q.val (Sum.inr x) (Sum.inr x_1) else 0 := by
    intro x
    rw [Finset.sum_eq_zero, zero_add, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x_1 _ => ?_
      by_cases h : (x_1 : ℕ) = x + 1
      · rw [if_pos ⟨by omega, by omega⟩, if_pos h, h]
        have hϖ : (ϖ : K) ≠ 0 := ϖ.ne_zero
        field_simp
        ring
      · rw [if_neg (by omega), if_neg h, mul_zero]
    · intro x_1 _
      rw [if_neg]
      have := x_1.2
      omega
  simp only [A, B, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
  rfl


theorem redFn_conj_eq_one {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {a e : AE D} {P : Finset (Pl D.host.E)}
    {PP Q : Pl D.host.E} (ha : IsIdemSum a P) (hPP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) {n : GA D V}
    (hn : SuppAt e V n) (t : GA D V) (hS : finE V (t⁻¹ * n * t) ∈ St β) (hQ : Q ∈ P) (hne : PP ≠ Q) :
    redFn β Q (finE V (t⁻¹ * n * t)) = 1 := by
  refine GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne ha hPP he ?_ hS hQ hne
  intro i j
  have h2 : mt V t⁻¹ * mt V t = 1 := by
    show mt V (t⁻¹ * t) = 1
    rw [inv_mul_cancel]; rfl
  have e1 : mt V (t⁻¹ * n * t) - 1 = mt V t⁻¹ * (mt V n - 1) * mt V t := by
    show mt V t⁻¹ * mt V n * mt V t - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
  rw [e1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have := hn m l
  linear_combination (mt V t⁻¹ i m * mt V t l j) * this

end GlobalTheory.NChainChar
end

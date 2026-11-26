module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubquotient
namespace GlobalTheory.QuotientGenerator

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def gen (ρ : Representation ℂ G V) (x : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g x)
  apply_mem_toSubmodule g v hv := by
    have h : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤ Submodule.span ℂ (Set.range fun g => ρ g x) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    exact h ⟨v, hv, rfl⟩

theorem self_mem_gen (ρ : Representation ℂ G V) (x : V) : x ∈ (gen ρ x).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem eq_top_of_mem (ρ : Representation ℂ G V) (x : V) (M : Subrepresentation (gen ρ x).toRepresentation)
    (hx : (⟨x, self_mem_gen ρ x⟩ : (gen ρ x).toSubmodule) ∈ M.toSubmodule) : M.toSubmodule = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have h : (gen ρ x).toSubmodule ≤ M.toSubmodule.map (gen ρ x).toSubmodule.subtype := by
    change Submodule.span ℂ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, M.apply_mem_toSubmodule g hx, rfl⟩
  obtain ⟨w, hw, rfl⟩ := h hv
  exact hw

theorem exists_maximal (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ M : Subrepresentation ρ, Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M := by
  have key := zorn_le_nonempty₀ {N : Subrepresentation ρ | x ∉ N.toSubmodule} ?_ ⊥ hx
  · obtain ⟨m, -, hm⟩ := key
    exact ⟨m, hm⟩
  intro c hc hch y hy
  have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
  have hd : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨d, hd, h1, h2⟩ := hch.directedOn a ha b hb
    exact ⟨_, ⟨d, hd, rfl⟩, h1, h2⟩
  refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), fun g v hv => ?_⟩, fun h => ?_, fun z hz => ?_⟩
  · rw [Submodule.mem_sSup_of_directed hne hd] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, a.apply_mem_toSubmodule g hv⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := (Submodule.mem_sSup_of_directed hne hd).1 h
    exact hc ha hv
  · exact (le_sSup ⟨z, hz, rfl⟩ : z.toSubmodule ≤ sSup (Subrepresentation.toSubmodule '' c))

noncomputable def quot (ρ : Representation ℂ G V) (M : Subrepresentation ρ) : Representation ℂ G (V ⧸ M.toSubmodule) :=
  ρ.quotient M.toSubmodule fun g _ hv => M.apply_mem_toSubmodule g hv

theorem quot_mk (ρ : Representation ℂ G V) (M : Subrepresentation ρ) (g : G) (v : V) :
    quot ρ M g (M.toSubmodule.mkQ v) = M.toSubmodule.mkQ (ρ g v) := rfl

theorem quot_irreducible (ρ : Representation ℂ G V) (x : V)
    (hcyc : ∀ N : Subrepresentation ρ, x ∈ N.toSubmodule → N.toSubmodule = ⊤) (M : Subrepresentation ρ)
    (hM : Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M) : (quot ρ M).IsIrreducible := by
  have hx0 : M.toSubmodule.mkQ x ≠ 0 := fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h)
  haveI : Nontrivial (Subrepresentation (quot ρ M)) := ⟨⟨⊥, ⊤, fun h => hx0 (by
    have h1 : M.toSubmodule.mkQ x ∈ (⊤ : Subrepresentation (quot ρ M)).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact h1)⟩⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation ρ := ⟨T.toSubmodule.comap M.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  by_cases hx : x ∈ T'.toSubmodule
  · right
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    have : v ∈ T'.toSubmodule := by rw [hcyc T' hx]; trivial
    exact this
  · left
    have hle : M ≤ T' := fun v hv => by
      change M.toSubmodule.mkQ v ∈ T.toSubmodule
      have : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
      rw [this]
      exact zero_mem _
    have hge : T' ≤ M := hM.2 hx hle
    apply Subrepresentation.toSubmodule_injective
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 (hge (show v ∈ T' from hw))

theorem exists_irreducible_subquotient (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V)
    (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      Representation.IsIrreducible τ ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
      ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
        ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y := by
  let x' : (gen ρ x).toSubmodule := ⟨x, self_mem_gen ρ x⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  obtain ⟨M, hM⟩ := exists_maximal (gen ρ x).toRepresentation x' hx'
  refine ⟨_, inferInstance, inferInstance, quot _ M, M.toSubmodule.mkQ x',
    quot_irreducible _ x' (eq_top_of_mem ρ x) M hM,
    ⟨gen ρ x, ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext fun v => (quot_mk _ M g v).symm⟩, M.toSubmodule.mkQ_surjective⟩,
    fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h), fun ι s f c b h => ?_⟩
  have h' : ∑ i ∈ s, c i • (gen ρ x).toRepresentation (f i) x' = b • x' := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h
  have h2 := congrArg M.toSubmodule.mkQ h'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul] at h2
  simpa only [map_smul, quot_mk] using h2

end GlobalTheory.QuotientGenerator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacTypeVec

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock GlobalTheory.JacBlockTwo ValuativeRel Matrix

theorem exists_irreducible_subquotient_rel (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
          ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y :=
  _root_.GlobalTheory.QuotientGenerator.exists_irreducible_subquotient G V ρ x hx

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mulSingle_false_mem_KO {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (a : Bool) :
    (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) a ∈ KO F (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_same]; exact hg
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _

theorem deltaHalf_mulSingle_false {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) :
    deltaHalf F (Two (Fin r) (Fin t)) (Pi.mulSingle false g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow F _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_false_mem_KO (t := t) hg a)

theorem emb₂_one_eq {r t : ℕ} (g : GL (Fin r) F) :
    emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) =
      leviEmb F (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
  unfold emb₂
  rw [MonoidHom.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem jac_mulSingle_false {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin (r + t)) F) W) {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (v : W) :
    GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle false g) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v) := by
  rw [jac_mk, deltaHalf_mulSingle_false hg, inv_one, Units.val_one, one_smul, emb₂_one_eq]

theorem act_mulSingle_false_KOne {r t : ℕ} {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) F) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin r) F} (hg : g ∈ KOne F (Fin r)) :
    π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v = v := by
  set h := emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) with hdef
  have hval : ∀ i j, h.val i j = Matrix.reindex (stdSum (rfl : r + t = r + t)) (stdSum (rfl : r + t = r + t))
      (Matrix.fromBlocks g.val 0 0 (1 : GL (Fin t) F).val) i j := fun i j => by
    rw [hdef]
    exact congrFun (congrFun (val_emb₂ F _ (g, 1)) i) j
  have hKO : h ∈ KO F (Fin (r + t)) := by
    have hg' : g ∈ KO F (Fin r) := GlobalTheory.StepData.KOne_le_KO hg
    have e : h = leviEmb F (two (stdSum (rfl : r + t = r + t)))
        (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
      rw [hdef, emb₂_one_eq]
    rw [e]
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_false_mem_KO hg' a), ?_⟩
    rw [← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_false_mem_KO hg' a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [hval, ← stdSum_inr', ← stdSum_inl']
    simp
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = g.val i j := fun i j => by
    rw [hval, ← stdSum_inl', ← stdSum_inl']
    simp
  have h2 : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, hval, ← stdSum_inr', ← stdSum_inr']
    simp
  have hg1 := GlobalTheory.StepData.mem_KOne.1 hg
  have key := hv h hKO (fun i j => by simp [h0]) (fun i j => by
      rw [h1]; have := hg1 i j; simpa [Matrix.sub_apply, Matrix.one_apply] using this) 1
    (by rw [h2, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

end Local

theorem exists_subquot_typeVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  intro hP F _ _ _ _ p _ r t χ W _ _ π z y ℓ hp hsm hirr hχ hy0 hy hℓ hz
  obtain ⟨hx0, hxt⟩ := jacquet_ne_zero_of_isBlockVec_two hP F r t χ W π y hsm hirr hχ hy0 hy
  set x : Jacquet π (unipRad F (two (stdSum (rfl : r + t = r + t)))) := Submodule.Quotient.mk y with hxdef
  obtain ⟨Y, _, _, τ, w, hτ, hsq, hw0, hrel⟩ :=
    exists_irreducible_subquotient_rel _ _ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π) x hx0
  refine ⟨Y, inferInstance, inferInstance, τ, hτ, hsq, w, hw0, fun g hg => ?_, ?_, ℓ, hℓ, ?_⟩
  · have := hrel Unit {()} (fun _ => Pi.mulSingle true g) (fun _ => 1) _ (by
      simpa using hxt g hg)
    simpa using this
  · intro h hh
    have := hrel Unit {()} (fun _ => Pi.mulSingle false h) (fun _ => 1) 1 (by
      simp only [Finset.sum_singleton, one_smul]
      rw [hxdef, jac_mulSingle_false π (GlobalTheory.StepData.KOne_le_KO hh), act_mulSingle_false_KOne hy hh])
    simpa using this
  · have hsum : ∑ g ∈ z.coeff.support, z.coeff g • GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π
        (Pi.mulSingle false (ℓ g)) x = (1 : ℂ) • x := by
      rw [one_smul, hxdef]
      have e : ∀ g ∈ z.coeff.support, z.coeff g • GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π
          (Pi.mulSingle false (ℓ g)) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (z.coeff g • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) :=
        fun g _ => by rw [jac_mulSingle_false π ((hℓ g).mem_KO hp), Submodule.Quotient.mk_smul]
      rw [Finset.sum_congr rfl e]
      conv_rhs => rw [← hz, Finsupp.sum]
      exact (map_sum (Submodule.mkQ _) _ _).symm
    have := hrel _ z.coeff.support (fun g => Pi.mulSingle false (ℓ g)) z.coeff 1 hsum
    rw [one_smul] at this
    intro h0
    apply hw0
    rw [← this, ← h0, Finsupp.sum]
    rfl

end GlobalTheory.JacTypeVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariantStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_parahoric_invariant : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  first | exact @GlobalTheory.JacTypeVec.exists_subquot_typeVec | exact GlobalTheory.JacTypeVec.exists_subquot_typeVec | (intros; apply GlobalTheory.JacTypeVec.exists_subquot_typeVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupMove
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupRelIffSameData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7}

theorem exists_setupRel (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (ρ : Setup X) :
    ∃ ρ' : Setup X', SetupRel ρ ρ' := by
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  dsimp only at a1 a2 a3
  subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  obtain ⟨rc, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  rename_i fin
  refine ⟨@Setup.mk _ _ _ ⟨rc.κ, rc.art⟩ ch bad e ek
    (fun i j b => ⟨(B i j b).hr, ⟨(B i j b).F.ψ, (B i j b).F.θ, (B i j b).F.sT, (B i j b).F.BS, (B i j b).F.BT, (B i j b).F.ΛS,
      (B i j b).F.ΛT, (B i j b).F.βS, (B i j b).F.βT, (B i j b).F.f₀⟩, ⟨(B i j b).G.Pg, (B i j b).G.P, (B i j b).G.mu⟩,
      ⟨(B i j b).de.Q, (B i j b).de.chi, (B i j b).de.res⟩,
      ⟨(B i j b).w.p, (B i j b).w.q, (B i j b).w.ap, (B i j b).w.am, (B i j b).w.c, (B i j b).w.lam⟩, (B i j b).mu0, (B i j b).eta⟩)
    om (fun i j b t => Cl i j b ⟨t.Q, t.chi, t.res⟩) (fun i j b t => fin i j b ⟨t.Q, t.chi, t.res⟩)
    (fun i j b t => rep i j b ⟨t.Q, t.chi, t.res⟩) β eG,
    ⟨.rfl, .rfl⟩, .rfl, .rfl, .rfl, .rfl, ?_, .rfl, ?_, ?_, .rfl, ?_⟩
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact ⟨⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩, ⟨.rfl, .rfl, .rfl⟩,
      ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩, .rfl, .rfl⟩
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    rfl
  · rintro i i' hi j j' hj b ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨r1, r2, r3⟩
    cases hi; cases Fin.ext hj; cases r1; cases r2; cases r3
    exact HEq.rfl
  · intro i i' hi j j' hj b
    cases hi; cases Fin.ext hj
    exact HEq.rfl

theorem RecipRel.good (h : SameGeo D D') {Ω Ω' : Type} [i1 : Field Ω] [i2 : Algebra D.host.E Ω] [i1' : Field Ω']
    [i2' : Algebra D'.host.E Ω'] (hΩ : Ω = Ω') (h1 : HEq i1 i1') (h2 : HEq i2 i2') {a : Recip D Ω} {a' : Recip D' Ω'}
    (r : RecipRel a a') (g : a.Good) : a'.Good := by
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  subst hΩ; subst h1; subst h2
  obtain ⟨κ, art⟩ := a
  obtain ⟨κ', art'⟩ := a'
  obtain ⟨r1, r2⟩ := r
  cases r1; cases r2
  exact ⟨g.1, g.2, g.3, g.4⟩

theorem SetupRel.good_of (h : SameGeo D D') {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (hδ : HEq X.delta X'.delta)
    (he : ∀ i i', HEq i i' → ∀ b x', ∃ x, HEq (sideEmb X i b x) (sideEmb X' i' b x') ∧ embLL0 D x = embLL0 D' x')
    {ρ : Setup X} {ρ' : Setup X'} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good := by
  have grc := r.rc.good h (eq_of_heq h1.Om) h1.instOm h1.algOm g.rc
  have h0 := h
  obtain ⟨gR, ghost, gsp, gTau, ginstTau, geTau, ghc⟩ := h
  obtain ⟨_, _, _, _, _, w, _⟩ := D
  obtain ⟨_, _, _, _, _, w', _⟩ := D'
  dsimp only at gR ghost gsp gTau ginstTau geTau ghc
  subst gR; subst ghost; subst gsp
  cases w; cases w'
  dsimp only at gTau ginstTau geTau ghc
  subst gTau; subst ginstTau; subst geTau; subst ghc
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  dsimp only at a1 a2 a3
  subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  dsimp only at hδ
  subst hδ
  obtain ⟨⟨κ, art⟩, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  obtain ⟨⟨κ', art'⟩, ch', bad', e', ek', B', om', Cl', rep', β', eG'⟩ := ρ'
  obtain ⟨⟨r1, r2⟩, r3, r4, r5, r6, r7, r8, r9, r10, -, -⟩ := r
  dsimp only at r1 r2 r3 r4 r5 r6 r8
  subst r1 r2 r3 r4 r5 r6 r8
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces, g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces, fun i b x' => ?_, g.ek_e,
    fun i j b => (r7 i i .rfl j j rfl b).good h0 .rfl .rfl (g.base i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).1 (g.latS i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.1 (g.latT i j b),
    fun i j b => ((r7 i i .rfl j j rfl b).isBaseFrame h0 .rfl .rfl).2.2 (g.Pg i j b), fun i j b => ?_, fun i j b t ht => ?_,
    fun i j b t ht ha => ?_⟩
  · obtain ⟨x, h3, h4⟩ := he i i .rfl b x'
    exact (congrArg (e i b) (eq_of_heq h3).symm).trans ((g.e_LL0 i b x).trans h4)
  · have t := (r7 i i .rfl j j rfl b).de
    rw [g.delta i j b] at t
    exact TwistRel.eq ⟨t.1.symm, t.2.symm, t.3.symm⟩
  · exact (r7 i i .rfl j j rfl b).isWeil h0 .rfl .rfl .rfl .rfl
      (g.weil i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht))
  · exact (r7 i i .rfl j j rfl b).isClassSystem h0 .rfl .rfl (t := ⟨t.Q, t.chi, t.res⟩) ⟨.rfl, .rfl, .rfl⟩
      (r9 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩) (r10 i i .rfl j j rfl b _ t ⟨.rfl, .rfl, .rfl⟩)
      (g.classes i j b ⟨t.Q, t.chi, t.res⟩ (TwistRel.good h0.symm ⟨.rfl, .rfl, .rfl⟩ ht)
        ((r7 i i .rfl j j rfl b).adm h0 .rfl .rfl .rfl ha))

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem mem_move {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') {T T' : Type} (hT : T = T')
    {p : T → Finset (Pl H.E)} {p' : T' → Finset (Pl H'.E)} {c : T → Set (Pl H.E)} {c' : T' → Set (Pl H'.E)} (hp : HEq p p')
    (hc : HEq c c') {i : T} {i' : T'} (hi : HEq i i') {P : Pl H.E} {P' : Pl H'.E} (hP : HEq P P') (g : P ∈ p i → P ∈ c i) :
    P' ∈ p' i' → P' ∈ c' i' := by
  subst hR; subst hH; subst hT hp hc hi hP
  exact g

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem heq_app {T T' A : Type} (hT : T = T') {f : T → A} {f' : T' → A} (hf : HEq f f') {i : T} {i' : T'} (hi : HEq i i') :
    f i = f' i' := by
  subst hT hf hi
  rfl

variable {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem SetupRel.good (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (g : ρ.Good) : ρ'.Good :=
  r.good_of h.sameGeo h.gal h.set h.delta (fun _ _ hi b x => ⟨e x, h.sideEmb_heq hi b x, h.embLL0_eq x⟩) g

theorem SetupRel.realPin (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (r : SetupRel ρ ρ') (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG ρ' := by
  have G := h.sameGeo
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ (j : ℕ) = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast (congrArg Ranks.m h.gal.R).symm j', cast_heq _ _, rfl⟩
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i' t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i' t' P' h1 h2
    exact mem_move h.gal.R h.gal.host h.Tw_eq h.set.pD r.ch (cast_heq h.Tw_eq.symm i') h4 (p.deltaPl _ t P h3) h2
  all_goals
    intro i' j' b
    obtain ⟨i, j, hi, hj⟩ := back i' j'
    have q := r.B i i' hi j j' hj b
    obtain ⟨hV, hW, rV, rW, hp, hm⟩ := G.spaces hj
  · exact chain q.F.ψ (p.psi i j b) m.ψ
  · exact chain q.F.θ (p.inf i j b) m.θ
  · exact chain q.F.sT (p.cartT i j b) ((m.MW j j' hj).cart_onb G hW).1
  · exact val_move h.Tau rV q.F.BS (m.BV j j' hj) (p.onbS i j b)
  · exact chain q.F.BT (p.onbT i j b) ((m.MW j j' hj).cart_onb G hW).2
  · exact chain q.F.ΛS (p.latS i j b) (m.ΛV j j' hj)
  · exact chain q.F.ΛT (p.latT i j b) (m.ΛW j j' hj)
  · exact chain q.F.βS (p.frS i j b) (m.βV j j' hj)
  · exact chain q.F.βT (p.frT i j b) (m.βW j j' hj)
  · exact chain q.F.f₀ (p.vac i j b) (m.vacP j j' hj)
  · exact chain q.G.Pg (p.Pg i j b) m.Pg
  · exact grp_move h.gal.R h.gal.host (eq_of_heq h.gal.PlG) (FWT.rank_Wc j) (FWT.rank_Wc j') q.G.Pg m.Pg
      (r.eG i i' hi j j' hj b) m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (hj ▸ m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact G.chrEq q.de.chi (heq_app h.Tw_eq h.set.l hi ▸ m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.w.ap (funext (p.ap i j b)) hp)
  · exact congrFun (chain q.w.am (funext (p.am i j b)) hm)

theorem BaseRel.sameBase {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : BaseRel B B') : SameBase B B' :=
  ⟨r.F.1, r.F.2, r.F.3, r.F.4, r.F.5, r.F.6, r.F.7, r.F.8, r.F.9, r.F.10, r.G.1, r.G.2, r.G.3, ⟨r.de.1, r.de.2, r.de.3⟩,
    r.w.1, r.w.2, r.w.3, r.w.4, r.w.5, r.w.6, r.mu0, r.eta⟩

theorem SameBase.baseRel {S T : HSp D} {S' T' : HSp D'} {B : Base S T} {B' : Base S' T'} (r : SameBase B B') : BaseRel B B' :=
  ⟨⟨r.ψ, r.θ, r.sT, r.BS, r.BT, r.ΛS, r.ΛT, r.βS, r.βT, r.f₀⟩, ⟨r.Pg, r.P, r.mu⟩, ⟨r.de.1, r.de.2, r.de.3⟩,
    ⟨r.p, r.q, r.ap, r.am, r.c, r.lam⟩, r.mu0, r.eta⟩

theorem setupRel_iff_sameData {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} : SetupRel ρ ρ' ↔ SameData ρ ρ' :=
  ⟨fun r => ⟨r.rc.1, r.rc.2, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).sameBase, r.om,
      fun i i' hi j j' hj b t t' ht => ⟨r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩, r.rep i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩⟩,
      r.β, r.eG⟩,
    fun r => ⟨⟨r.κ, r.art⟩, r.ch, r.bad, r.e, r.ek, fun i i' hi j j' hj b => (r.B i i' hi j j' hj b).baseRel, r.om,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).1,
      fun i i' hi j j' hj b t t' ht => (r.Cl i i' hi j j' hj b t t' ⟨ht.1, ht.2, ht.3⟩).2, r.β, r.eG⟩⟩

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨ρ', r⟩ := exists_setupRel h.sameGeo h.gal h.set ρ
  exact ⟨ρ', setupRel_iff_sameData.1 r, r.good h g, r.realPin h m p⟩

end GlobalTheory.TwInputs.Move

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

theorem setup_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameSetup ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' :=
  fun h _ _ m ρ g p => setup_move_data h m ρ g p

end GlobalTheory.TwInputs.Move
end

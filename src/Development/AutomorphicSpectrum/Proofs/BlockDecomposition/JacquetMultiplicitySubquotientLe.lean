module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.JmMono

section General

variable {F G U V W : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem occursTimes_of_isSubquotient {σ : Representation F G U} {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) {r : ℕ} (ho : OccursTimes σ π r) :
    OccursTimes σ P r := by
  obtain ⟨S, f, hf⟩ := h
  unfold GlobalTheory.SmGL.OccursTimes at ho ⊢
  obtain ⟨A, B, hBA, hAB, hiso⟩ := ho
  let ι : Representation.IntertwiningMap S.toRepresentation P :=
    ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hι : Function.Injective ι := fun a b hab => Subtype.val_injective hab
  refine ⟨fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (A i)),
    fun i => GlobalTheory.JHMult.subMap ι (GlobalTheory.JHMult.subComap f (B i)),
    fun i => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hBA i)),
    fun i j hij => GlobalTheory.JHMult.subMap_mono ι (GlobalTheory.JHMult.subComap_mono f (hAB i j hij)),
    fun i => ?_⟩
  exact GlobalTheory.JHMult.step_iff.mpr
    (GlobalTheory.JHMult.step_map ι hι
      (GlobalTheory.JHMult.step_comap f hf
        (GlobalTheory.JHMult.step_iff.mp (hiso i))))

theorem jhMult_le_of_isSubquotient (σ : Representation F G U) {π : Representation F G V}
    {P : Representation F G W} (h : IsSubquotient π P) : jhMult σ π ≤ jhMult σ P := by
  unfold GlobalTheory.SmGL.jhMult
  exact iSup₂_le fun r hr => le_iSup₂_of_le r (GlobalTheory.CompanionTheory.JmMono.occursTimes_of_isSubquotient h hr) le_rfl

end General

theorem jm_le_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P) :
    jm y hy π ≤ jm y hy P := by
  unfold Zc.jm
  exact GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient _
    (GlobalTheory.JacquetExact.isSubquotient_jac _ hP h)

end GlobalTheory.CompanionTheory.JmMono

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_subquotient_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P), jm y hy π ≤ jm y hy P := by
  first | exact @GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | exact GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTerm

theorem term_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : Function.Injective Δ.term :=
  Segment.term_injective Δ

end GlobalTheory.CompanionTheory.SegTerm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_term_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), Function.Injective Δ.term := by
  first | exact @GlobalTheory.CompanionTheory.SegTerm.term_injective | exact GlobalTheory.CompanionTheory.SegTerm.term_injective | (intros; apply GlobalTheory.CompanionTheory.SegTerm.term_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FineStep

theorem isSubquotient_subQuot_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {J : Representation ℂ G V} (S R : Subrepresentation J) : IsSubquotient (subQuot S R) J := by
  refine GlobalTheory.SmGL.IsSubquotient.trans (σ := S.toRepresentation) ?_ ?_
  · refine GlobalTheory.SmGL.IsSubquotient.of_surjective
      ⟨(Submodule.comap S.toSubmodule.subtype R.toSubmodule).mkQ, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Submodule.mkQ_surjective _
  · refine GlobalTheory.SmGL.IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Subtype.val_injective

theorem nonempty_equiv_of_jhMult_eq_one :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J →
      jhMult T J = 1 →
      (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible →
        IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  intro G V W _ _ _ _ _ T J hT hfin hJ hall
  have hstep : ∀ {P Q : Subrepresentation J}, Q ⋖ P → GlobalTheory.JHMult.Step T P Q := fun {P Q} h =>
    GlobalTheory.JHMult.step_iff.mp
      (hall _ (subQuot P Q) (GlobalTheory.SmGL.isIrreducible_subQuot h) (isSubquotient_subQuot_self P Q))
  have hwf : WellFounded ((· < ·) : Subrepresentation J → Subrepresentation J → Prop) := by
    haveI : IsArtinian (MonoidAlgebra ℂ G) J.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (show IsFiniteLength (MonoidAlgebra ℂ G) J.asModule from hfin)).2
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := J)).toOrderEmbedding.ltEmbedding.wellFounded
      wellFounded_lt
  have hne : (⊥ : Subrepresentation J) ≠ ⊤ := by
    intro h
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      have hb : b ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      rw [← h] at ha hb
      rw [(Submodule.mem_bot ℂ).mp ha, (Submodule.mem_bot ℂ).mp hb]⟩
    have h0 := GlobalTheory.SmGL.jhMult_of_subsingleton hT J
    rw [hJ] at h0
    exact one_ne_zero h0
  have hirr : J.IsIrreducible := by
    show IsSimpleOrder (Subrepresentation J)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    by_contra hS
    obtain ⟨hS0, hS1⟩ := not_or.mp hS
    obtain ⟨A, ⟨hA0, hAS⟩, hAmin⟩ := hwf.has_min {A | ⊥ < A ∧ A ≤ S}
      ⟨S, show ⊥ < S ∧ S ≤ S from ⟨bot_lt_iff_ne_bot.mpr hS0, le_rfl⟩⟩
    obtain ⟨B, hB, hBmin⟩ := hwf.has_min {B | S < B}
      ⟨⊤, show S < ⊤ from lt_top_iff_ne_top.mpr hS1⟩
    have hcA : (⊥ : Subrepresentation J) ⋖ A := ⟨hA0, by
      intro c hc hcA
      exact hAmin c (show ⊥ < c ∧ c ≤ S from ⟨hc, hcA.le.trans hAS⟩) hcA⟩
    have hSB : S < B := hB
    have hcB : S ⋖ B := ⟨hSB, by
      intro c hc hcB
      exact hBmin c (show S < c from hc) hcB⟩
    have hocc : GlobalTheory.SmGL.OccursTimes T J 2 := by
      have := GlobalTheory.JHMult.occurs_of_finset (σ := T) (ρ := J) (r := 2) Finset.univ ![A, B] ![⊥, S]
        (by simp [Fin.forall_fin_two, hSB.le]) (by simp [Fin.forall_fin_two, hAS])
        (by simp [Fin.forall_fin_two, hstep hcA, hstep hcB])
      simpa using this
    have h2 : ((2 : ℕ) : ℕ∞) ≤ GlobalTheory.SmGL.jhMult T J := by
      unfold GlobalTheory.SmGL.jhMult
      exact le_iSup₂_of_le 2 hocc le_rfl
    rw [hJ] at h2
    have h21 : ¬ ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_le_natCast]
      omega
    exact h21 (by simpa using h2)
  exact hall V J hirr (GlobalTheory.SmGL.IsSubquotient.refl J)

end GlobalTheory.CompanionTheory.FineStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactorStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_multiplicity_one_unique_factor : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J → jhMult T J = 1 → (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible → IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  first | exact @GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | exact GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | (intros; apply GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.CompanionTheory.SegFine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {n : ℕ}

abbrev ev (k : Type) [Field k] (n : ℕ) : (∀ _ : Fin 1, GL (Fin n) k) →* GL (Fin n) k :=
  Pi.evalMonoidHom (fun _ : Fin 1 => GL (Fin n) k) 0

abbrev lv (τ : Representation ℂ (GL (Fin n) k) X) : Representation ℂ (∀ _ : Fin 1, GL (Fin n) k) X := τ.comp (ev k n)

theorem stdBlocks_one (h : ∑ _ : Fin 1, n = n) (a : Fin 1) (i : Fin n) :
    stdBlocks (fun _ : Fin 1 => n) h ⟨a, i⟩ = i :=
  Fin.ext (by rw [stdBlocks_val, Subsingleton.elim a 0]; simp)

theorem leviEmb_one (h : ∑ _ : Fin 1, n = n) (g : ∀ _ : Fin 1, GL (Fin n) k) :
    leviEmb k (stdBlocks (fun _ : Fin 1 => n) h) g = g 0 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := leviEmb_apply_same k (stdBlocks (fun _ : Fin 1 => n) h) g 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

theorem unipRad_one (h : ∑ _ : Fin 1, n = n) : unipRad k (stdBlocks (fun _ : Fin 1 => n) h) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => Units.ext (Matrix.ext fun i j => ?_)
  have := (mem_unipRad.1 hu).2 0 i j
  rwa [stdBlocks_one, stdBlocks_one] at this

def jacEquiv (h : ∑ _ : Fin 1, n = n) (π : Representation ℂ (GL (Fin n) k) V) :
    (lv π).Equiv (SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) := by
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 = ⊥ := by
    rw [unipRad_one]
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp
  have hd : ∀ g, deltaHalf k (fun _ : Fin 1 => Fin n) g = 1 := fun g => by
    simp [deltaHalf_apply, modExp, Finset.filter_singleton]
  let f : (lv π).IntertwiningMap (SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) :=
    ⟨(twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1).mkQ, fun g => LinearMap.ext fun v => by
      show Submodule.Quotient.mk (π (g 0) v) = SmGL.jac _ π g (Submodule.Quotient.mk v)
      rw [jac_mk, hd, leviEmb_one]
      simp⟩
  refine equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun v hv => ?_, Submodule.Quotient.mk_surjective _⟩
  have : v ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin 1 => n) h)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  rw [hK] at this
  exact this

def piTensorEquiv (τ : Representation ℂ (GL (Fin n) k) X) :
    (lv τ).Equiv (piTensor fun _ : Fin 1 => τ) := by
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => X) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  let f : (lv τ).IntertwiningMap (piTensor fun _ : Fin 1 => τ) :=
    ⟨L.toLinearMap, fun g => LinearMap.ext fun v => by
      show L (τ (g 0) v) = piTensor (fun _ : Fin 1 => τ) g (L v)
      rw [hL, hL, piTensor_tprod]
      exact congrArg _ (funext fun a => by rw [Subsingleton.elim a 0])⟩
  exact equivOfBijective f L.bijective

def subrepComp (τ : Representation ℂ (GL (Fin n) k) X) :
    Subrepresentation (lv τ) ≃o Subrepresentation τ where
  toFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (fun _ => g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (g 0) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {τ : Representation ℂ (GL (Fin n) k) X} (h : τ.IsIrreducible) :
    (lv τ).IsIrreducible := (subrepComp τ).isSimpleOrder_iff.2 h

theorem jhMult_one (h : ∑ _ : Fin 1, n = n) (τ : Representation ℂ (GL (Fin n) k) X)
    (π : Representation ℂ (GL (Fin n) k) V) :
    jhMult (piTensor fun _ : Fin 1 => τ) (SmGL.jac (stdBlocks (fun _ : Fin 1 => n) h) π) =
      jhMult (lv τ) (lv π) := by
  rw [← jhMult_congr_left (piTensorEquiv τ), ← jhMult_congr_right _ (jacEquiv h π)]

theorem jm_eq_one (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (hyx : y = fun _ => x) : jm y hy π = 1 := by
  subst hyx
  refine (jhMult_one hy x.rep π).trans ?_
  rw [jhMult_congr_right _ (compEquiv φ (ev k x.1))]
  exact jhMult_self (isIrreducible_comp x.2.rep.irr)

theorem eq_of_one_le_jm (x : IrrGL (k := k)) (π : Representation ℂ (GL (Fin x.1) k) V) (φ : π.Equiv x.rep)
    (y : Fin 1 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1) (h : 1 ≤ jm y hy π) : y 0 = x := by
  obtain ⟨z, rfl⟩ : ∃ z, y = fun _ => z := ⟨y 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨d, c⟩ := z
  obtain ⟨m, b⟩ := x
  obtain rfl : d = m := by simpa using hy
  have h0 : jhMult (lv c.rep.ρ) (lv π) ≠ 0 := by
    rw [← jhMult_one hy]
    exact ENat.one_le_iff_ne_zero.1 h
  have hπ : π.IsIrreducible := isIrreducible_of_equiv φ.symm b.rep.irr
  obtain ⟨E⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv (isIrreducible_comp c.rep.irr) (isIrreducible_comp hπ)
  let f : π.IntertwiningMap c.rep.ρ := ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun v =>
    E.toIntertwiningMap.isIntertwining _ _ (fun _ => g) v⟩
  have E' : c.rep.ρ.Equiv b.rep.ρ := (equivOfBijective f E.toLinearEquiv.bijective).symm.trans φ
  exact congrArg (Sigma.mk d) (irrCl_eq_iff.2 ⟨E'⟩)

theorem dec_single (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : dec (Segment.single ρ hρ) = fun _ => ρ := funext fun a => by
  show ρ.nu (((Fin.rev (a : Fin 1) : Fin 1) : ℕ) : ℂ) = ρ
  simp [Fin.val_eq_zero]

theorem not_one_le_jm {N c : ℕ} {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsCuspidal π)
    (y : Fin (c + 2) → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (hc : ∀ a, (y a).IsCusp) : ¬ 1 ≤ jm y hy π := by
  intro h
  have hne : unipRad k (stdBlocks (fun a => (y a).1) hy) ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2
    ⟨stdBlocks (fun a => (y a).1) hy ⟨0, ⟨0, (hc 0).1⟩⟩, stdBlocks (fun a => (y a).1) hy ⟨1, ⟨0, (hc 1).1⟩⟩, by simp⟩
  have := hπ.2 _ _ _ hne
  have hn : Nontrivial (PiTensorProduct ℂ fun a => (y a).2.rep.V) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ fun a => Model.nontrivial_of_isIrreducible (y a).2.rep.irr
  obtain ⟨S, f, hf⟩ := jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h)
  exact not_subsingleton _ hf.subsingleton

theorem fineJac_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJac Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  obtain rfl : ρ.1 = N := by
    have := hπ.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique hπ
  refine ⟨fun hd => jm_eq_one ρ π φ _ hd (dec_single ρ hρ), fun c y hy hc h1 => ?_⟩
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL (k := k)) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (dec_single ρ hρ) _).symm⟩
  · exact absurd h1 (not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

end GlobalTheory.CompanionTheory.SegFine

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_length_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_one | exact GlobalTheory.CompanionTheory.SegFine.fineJac_one | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FrobInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mk_parab (e : (Σ a, m a) ≃ n) (τ : Representation ℂ (GL n k) V) (p : parab k e) (w : V) :
    (Submodule.Quotient.mk (τ (p : GL n k) w) : Jacquet τ (unipRad k e)) =
      Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) w) := by
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k e p
  have key : ∀ y : V, (Submodule.Quotient.mk (τ u y) : Jacquet τ (unipRad k e)) = Submodule.Quotient.mk y := by
    intro y
    rw [Submodule.Quotient.eq]
    apply Submodule.subset_span
    refine Set.mem_ofPred.mpr ⟨⟨u, hu⟩, y, ?_⟩
    simp
  have hL : ∀ y : V, (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) y) : Jacquet τ (unipRad k e)) =
      ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • SmGL.jac e τ (leviProj k e p) (Submodule.Quotient.mk y) := by
    intro y
    rw [jac_mk, smul_smul, Units.mul_inv, one_smul]
  have e1 : τ (p : GL n k) w = τ (leviEmb k e (leviProj k e p)) (τ u w) := by
    first
    | (rw [hp, map_mul]; rfl)
    | rw [hp, map_mul]
  rw [e1, hL, hL, key]

def frobFun (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) : GL n k → W :=
  fun g => f (Submodule.Quotient.mk (τ g v))

theorem frobFun_law (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) (p : parab k e) (g : GL n k) :
    frobFun e f v (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (frobFun e f v g) := by
  have h1 : frobFun e f v (p * g) =
      f (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) := by
    show f (Submodule.Quotient.mk (τ ((p : GL n k) * g) v)) = _
    rw [map_mul]
    exact congrArg f (mk_parab e τ p (τ g v))
  have h2 := LinearMap.congr_fun (f.isIntertwining' (leviProj k e p)) (Submodule.Quotient.mk (τ g v))
  simp only [LinearMap.comp_apply] at h2
  rw [h1]
  show f.toLinearMap (Submodule.Quotient.mk (τ (leviEmb k e (leviProj k e p)) (τ g v))) =
    ((deltaHalf k m (leviProj k e p) : ℂˣ) : ℂ) • ρ (leviProj k e p) (f.toLinearMap (Submodule.Quotient.mk (τ g v)))
  rw [← h2, jac_mk, map_smul, smul_smul, Units.mul_inv, one_smul]

theorem frobFun_mem (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    frobFun e f v ∈ indSpace (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) := by
  show ∀ (h : ↥(parab k e)) (g : GL n k),
    frobFun e f v (↑h * g) = ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) h (frobFun e f v g)
  intro p x
  rw [frobFun_law, MonoidHom.comp_apply, twist_apply]

theorem frobFun_translate (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) (h x : GL n k) :
    frobFun e f v (x * h) = frobFun e f (τ h v) x := by
  show f (Submodule.Quotient.mk (τ (x * h) v)) = f (Submodule.Quotient.mk (τ x (τ h v)))
  first
  | (rw [map_mul]; rfl)
  | rw [map_mul]

theorem frobFun_smooth (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    (⟨frobFun e f v, frobFun_mem e f v⟩ : indSpace (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) ∈
      smoothPart (ind (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) := by
  show IsOpen {g : GL n k | (ind (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e))) g
    ⟨frobFun e f v, frobFun_mem e f v⟩ = ⟨frobFun e f v, frobFun_mem e f v⟩}
  set F : indSpace (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) :=
    ⟨frobFun e f v, frobFun_mem e f v⟩ with hF
  set R := ind (parab k e) ((SmGL.twist ρ (deltaHalf k m)).comp (leviProj k e)) with hR
  have hstab : ∀ s, τ s v = v → R s F = F := by
    intro s hs
    apply Subtype.ext
    funext x
    show frobFun e f v (x * s) = frobFun e f v x
    rw [frobFun_translate, hs]
  rw [isOpen_iff_forall_mem_open]
  intro g0 hg0
  refine ⟨(fun g => g0⁻¹ * g) ⁻¹' {g | τ g v = v}, ?_, IsOpen.preimage (continuous_const_mul g0⁻¹) (hτ v), ?_⟩
  · intro g hg
    have h1 : R (g0 * (g0⁻¹ * g)) F = R g0 (R (g0⁻¹ * g) F) := by
      first
      | (rw [map_mul]; rfl)
      | rw [map_mul]
    rw [mul_inv_cancel_left] at h1
    show R g F = F
    rw [h1, hstab _ hg]
    exact hg0
  · show τ (g0⁻¹ * g0) v = v
    rw [inv_mul_cancel, map_one]
    rfl

def frobInv (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (SmGL.jac e τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (parInd e ρ) where
  toLinearMap :=
    { toFun := fun v => ⟨⟨frobFun e f v, frobFun_mem e f v⟩, frobFun_smooth e hτ f v⟩
      map_add' := fun v w => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (v + w))) = f (Submodule.Quotient.mk (τ g v)) + f (Submodule.Quotient.mk (τ g w))
        rw [map_add (f := _), Submodule.Quotient.mk_add, map_add (f := _)]
      map_smul' := fun c v => by
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        show f (Submodule.Quotient.mk (τ g (c • v))) = c • f (Submodule.Quotient.mk (τ g v))
        rw [map_smul, Submodule.Quotient.mk_smul, map_smul] }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (frobFun_translate e f v g x).symm

theorem frobInv_one (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (SmGL.jac e τ).IntertwiningMap ρ) (v : V) :
    (frobInv e hτ f v).1.1 1 = f (Submodule.Quotient.mk v) := by
  show f (Submodule.Quotient.mk (τ 1 v)) = f (Submodule.Quotient.mk v)
  first
  | (rw [map_one]; rfl)
  | rw [map_one]

theorem exists_frobInv_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} (hτ : IsSmooth τ)
    {ρ : Representation ℂ (Levi k m) W} (f : (SmGL.jac e τ).IntertwiningMap ρ) (hf : ∃ v, f v ≠ 0) :
    ∃ v, frobInv e hτ f v ≠ 0 := by
  obtain ⟨w, hw⟩ := hf
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨v, fun h => hw ?_⟩
  have h1 := frobInv_one e hτ f v
  rw [h] at h1
  exact h1.symm

theorem exists_map_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ)
    (f : (SmGL.jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep))
    (hf : ∃ v, f v ≠ 0) : ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  exact ⟨frobInv (stdBlocks (fun a => (x a).1) hd) hτ f, exists_frobInv_ne_zero _ hτ f hf⟩

end GlobalTheory.CompanionTheory.FrobInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzeroStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_reciprocity_nonzero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hτ : IsSmooth τ) (f : (jac (stdBlocks (fun a => (x a).1) hd) τ).IntertwiningMap (piTensor fun a => (x a).rep)) (hf : ∃ v, f v ≠ 0), ∃ g : τ.IntertwiningMap (prodIrr x hd), ∃ v, g v ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | exact GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg Matrix

namespace GlobalTheory.CompanionTheory.SegNu

theorem exists_ne_zero_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra h
  push_neg at h
  haveI := hi
  refine (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective ?_)
  show (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem eq_smul_of_eigenvector {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} {w : V}
    (hw : w ≠ 0) (hc : π z w = c • w) (v : V) : π z v = c • v := by
  haveI := hi
  let E : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : π z v = c • v := by
          simpa [sub_eq_zero] using hv
        have h1 : π z (π g v) = π g (π z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
        simp [sub_eq_zero, h1, hv'] }
  have hE : E ≠ ⊥ := fun h => hw (by
    have h1 : w ∈ E.toSubmodule := by
      show w ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      simp [sub_eq_zero, hc]
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1)
  have hT : E = ⊤ := (eq_bot_or_eq_top E).resolve_left hE
  have h2 : v ∈ E.toSubmodule := by
    rw [hT]
    exact Submodule.mem_top
  have h3 : v ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V)) := h2
  simpa [sub_eq_zero] using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_scalar {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (ha : IsAdmissible π) (hi : π.IsIrreducible) {z : GL (Fin n) k} (hz : ∀ g, z * g = g * z) :
    ∃ ω : ℂ, ∀ v, π z v = ω • v := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr hi
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        have ha' : π a v = v := ha
        show π a⁻¹ v = v
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set (GL (Fin n) k)) := ha.1 v
  let K : Subgroup (GL (Fin n) k) := S ⊓ KO k (Fin n)
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) Set.inter_subset_right
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hKo hKc
  have hvK : v ∈ fixed π K := fun h => by
    have h' : π (h : GL (Fin n) k) v = v := h.2.1
    simpa using h'
  haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  have hst : ∀ u ∈ fixed π K, π z u ∈ fixed π K := fun u hu h => by
    have hu' := hu h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hu' ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hu']
  let T : Module.End ℂ (fixed π K) := (π z).restrict hst
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have h1 : π z (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have h2 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  exact ⟨c, eq_smul_of_eigenvector hi hz h2 h1⟩

theorem eq_zero_of_nu_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hd : 0 < x.1) {s : ℝ}
    (hs : x.nu (s : ℂ) = x) : s = 0 := by
  have h1 := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k (s : ℂ)) (isSmoothChar_absPow _)
  rw [IrrGL.of_rep] at h1
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 (h1.symm.trans (hs.trans (IrrGL.of_rep x).symm))
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let z : GL (Fin x.1) k := GeneralLinearGroup.scalar (Fin x.1) ϖ
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = ϖ ^ x.1 := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨ω, hω⟩ := exists_scalar (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr hz
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr x.2.rep.irr
  have hω0 : ω ≠ 0 := fun e => hv (by
    have h2 : x.rep z⁻¹ (x.rep z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hω, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have h3 := LinearMap.congr_fun (φ.isIntertwining' z) v
  have hLv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h4 : φ.toLinearEquiv (((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) • x.rep z v) = x.rep z (φ.toLinearEquiv v) := by
    have h5 : φ.toLinearEquiv ((SmGL.twist x.rep (detChar _ (absPow k (s : ℂ)))) z v) = x.rep z (φ.toLinearEquiv v) := h3
    rwa [twist_apply, detChar_apply, hdet] at h5
  rw [hω, hω, map_smul, map_smul, smul_smul] at h4
  have h6 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) * ω = ω := smul_left_injective ℂ hLv h4
  have h7 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hω0 (h6.trans (one_mul ω).symm)
  have h8 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) ^ x.1 = 1 := by
    rw [← h7, map_pow, Units.val_pow_eq_pow_val]
  rw [val_absPow_ofReal] at h8
  have h9 : (nabs k ϖ ^ s) ^ x.1 = 1 := by exact_mod_cast h8
  have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
  have h10 : nabs k ϖ ^ s = 1 := (pow_eq_one_iff_of_nonneg (Real.rpow_nonneg hpos.le s) hd.ne').1 h9
  have hne : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h11 := congrArg Real.log h10
  rw [Real.log_rpow hpos, Real.log_one] at h11
  exact (mul_eq_zero.1 h11).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hpos hne)

theorem nu_natCast_inj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ)
    (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  intro k _ _ _ _ hA x hx a b h
  have h1 : x.nu (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) = x := by
    have h2 := congrArg (fun y => IrrGL.nu y (-(b : ℂ))) h
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
    rw [← h2]
    congr 1
    push_cast
    ring
  have h3 := eq_zero_of_nu_eq hA x hx.1 h1
  exact_mod_cast sub_eq_zero.1 h3

end GlobalTheory.CompanionTheory.SegNu
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.KerTwFin

section Rational

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem discreteTopology_range : DiscreteTopology (ratGL E n).range :=
  GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n

theorem isClosed_range : IsClosed ((ratGL E n).range : Set (GA E n)) :=
  GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL E n

theorem injective_ratGL : Function.Injective (ratGL E n) :=
  GroundTheory.Automorphic.AdelicGLn.diagonal_injective E n

theorem finite_ratGL_mem {K : Set (GA E n)} (hK : IsCompact K) : {d : GL (Fin n) E | ratGL E n d ∈ K}.Finite := by
  have hcomp : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right isClosed_range
  have hdisc : DiscreteTopology ↥(K ∩ ((ratGL E n).range : Set (GA E n))) :=
    DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) discreteTopology_range inter_subset_right
  have hfin := hcomp.finite ⟨hdisc⟩
  refine (hfin.preimage (f := ratGL E n) injective_ratGL.injOn).subset fun d hd => ?_
  exact ⟨hd, d, rfl⟩

end Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_thetaA : Continuous (thetaA E n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h0 : Continuous fun g : GA E n => ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) :=
      Units.continuous_coe_inv
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · have h0 : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose

theorem finite_kernel {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C C' : Set (GA E n)} (hC : IsCompact C)
    (hC' : IsCompact C') :
    {d : GL (Fin n) E | ∃ x ∈ C, ∃ y ∈ C', φ (x⁻¹ * ratGL E n d * thetaA E n y) ≠ 0}.Finite := by
  have hK : IsCompact (C * tsupport φ * (thetaA E n '' C')⁻¹) :=
    (hC.mul hφ).mul (hC'.image continuous_thetaA).inv
  refine (finite_ratGL_mem hK).subset ?_
  rintro d ⟨x, hx, y, hy, h⟩
  have hd : ratGL E n d =
      x * (x⁻¹ * ratGL E n d * thetaA E n y) * (thetaA E n y)⁻¹ := by group
  change ratGL E n d ∈ C * tsupport φ * (thetaA E n '' C')⁻¹
  rw [hd]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ h))
    (Set.inv_mem_inv.2 (mem_image_of_mem _ hy))

theorem finite_twConj {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  (finite_kernel hφ hC hC).subset fun _ ⟨x, hx, h⟩ => ⟨x, hx, x, hx, h⟩

theorem finite_twConj_of_isTest {φ : GA E n → ℂ} (hφ : IsTest φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  finite_twConj hφ.supp hC

theorem kerFin : PositivityTheory.Rg.BcB.D4.KerFin := fun _ _ _ _ _ _ hφ _ hC => finite_twConj_of_isTest hφ hC

end GlobalTheory.CompanionTheory.KerTwFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.QdetCoeff

theorem coeff_mem_span_values {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) (a : ℕ → M)
    (f : ℂ → M) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range (n + 1), u ^ k • a k) (k : ℕ) (hk : k ≤ n) :
    a k ∈ Submodule.span ℂ (Set.range f) := by
  set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    simp only [hv, Nat.cast_inj] at h
    exact Fin.ext h
  set V := Matrix.vandermonde v
  have hdet : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set k' : Fin (n + 1) := ⟨k, by omega⟩
  have key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k := by
    simp_rw [hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j := by
      intro j
      rw [← hWV, Matrix.mul_apply]
      rfl
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [k']
  rw [← key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)


open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdet_eq_sum_coeff {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (w : ℂ) :
    Formalism.REAL.qdet E w = ∑ j ∈ Finset.range (n + 1), w ^ j • (qdetPoly E).coeff j := by
  rw [← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdetPoly_coeff_top {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    (qdetPoly E).coeff n = 1 := by
  rw [coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]

theorem qdet_shift_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ),
    ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  intro A _ _ n X c
  set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb
  set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
    intro u
    rw [qdet_eq_sum_coeff]
    have hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j =
        ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ)) := by
      intro j hj
      rw [add_pow]
      have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        have hj' := Finset.mem_range.mp hj
        intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]
    simp_rw [ha, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine ⟨a, ?_, ?_, hexp⟩
  · simp only [ha]
    rw [Finset.sum_eq_single n]
    · simp [hb, qdetPoly_coeff_top]
    · intro j hj hjn
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · intro k
    by_cases hk : k ≤ n
    · exact coeff_mem_span_values n a _ hexp k hk
    · have : a k = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [this]; exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.CTFin.QdetCoeff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficientsStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_polynomial_coefficients : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ), ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧ ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff | exact GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff | (intros; apply GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.FineProd

variable {k : Type} [Field k]

def dropHom {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) :
    Levi k (fun j => Fin (d j)) →* Levi k (fun a => Fin (d (o a))) where
  toFun g a := g (o a)
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.CompanionTheory.FineProd

end
end

module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvA
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem indS_apply (S : Finset (Pl D)) (v : Pl D) : (indS S) v = if v ∈ S then 1 else 0 := rfl

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem infPart_eS (S : Finset (Pl D)) : infPart D (eS S) = 1 := by
  simp only [infPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

theorem finPart_eS (S : Finset (Pl D)) :
    finPart D (eS S) = algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) := by
  simp only [finPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem cv_eq (v : Pl D) (z : AE D) :
    cv D v z = Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _), map_add (f := _)]
  | tmul a x => rfl

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

variable {D : D7}


open Classical in
theorem exists_int_off {K : Set (Af D.host.F)} (hK : IsCompact K) :
    ∃ T : Finset (Pl D), ∀ z ∈ K, ∀ v ∉ T, z v ∈ v.adicCompletionIntegers D.host.F := by
  classical
  let O : Finset (Pl D) → Set (Af D.host.F) :=
    fun T => {z | ∀ v, v ∉ T → z v ∈ (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))}
  have hO : ∀ T, IsOpen (O T) := fun T =>
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : Pl D => v.adicCompletion D.host.F)
      (A := fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have hcov : K ⊆ ⋃ T, O T := fun z _ => Set.mem_iUnion.2
    ⟨(Filter.eventually_cofinite.1 z.2).toFinset, fun v hv => by
      by_contra h
      exact hv ((Filter.eventually_cofinite.1 z.2).mem_toFinset.2 h)⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover O hO hcov fun T T' =>
    ⟨T ∪ T', fun z hz v hv => hz v fun h => hv (Finset.mem_union_left _ h),
      fun z hz v hv => hz v fun h => hv (Finset.mem_union_right _ h)⟩
  exact ⟨T, fun z hz v hv => hT hz v hv⟩

def sPart {a b : ℕ} (S : Finset (Pl D)) (y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i j => algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) * y i j


open Classical in
set_option maxHeartbeats 800000 in
theorem fin_good {a b : ℕ} (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ y, g y =
      if (∀ v ∉ S, ∀ i j, projV v y i j ∈ intLoc D.host.F D.host.E v)
      then g (sPart S y) else 0 := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  let B := Module.finBasis D.host.F D.host.E
  have hT1 : ∀ (i : Fin a) (j : Fin b) (k : Fin (Module.finrank D.host.F D.host.E)), ∃ T : Finset (Pl D),
      ∀ y ∈ tsupport g, ∀ v ∉ T, crd B (Af D.host.F) (y i j) k v ∈ v.adicCompletionIntegers D.host.F := by
    intro i j k
    have hc : Continuous fun y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E => y i j :=
      (continuous_apply j).comp (continuous_apply i)
    obtain ⟨T, hT⟩ := exists_int_off (D := D) (hcs.isCompact.image ((continuous_crd B (Af D.host.F) k).comp hc))
    exact ⟨T, fun y hy v hv => hT _ ⟨y, hy, rfl⟩ v hv⟩
  choose T1 hT1 using hT1
  have hU := invariant_mem_nhds hlc hcs
  let Lc : (Fin a → Fin b → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) →
      (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af D.host.F) ⊗ₜ[D.host.F] B k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af D.host.F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T2, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  have hinv : ∀ x u, (∀ i j k v, crd B (Af D.host.F) (u i j) k v ∈ P v) → g (x + u) = g x := by
    intro x u hu
    have hu' : u = Lc fun i j k => crd B (Af D.host.F) (u i j) k := by
      funext i j
      exact eq_sum_crd B (Af D.host.F) (u i j)
    rw [hu']
    exact h1 _ (fun i => h2 _ fun j => h3 _ fun k => hsub (hu i j k)) x
  have hbad := Filter.eventually_cofinite.1 (GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr B)
  refine ⟨(Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => Finset.univ.biUnion fun k => T1 i j k) ∪ T2 ∪
    hbad.toFinset, fun S hS y => ?_⟩
  have hS1 : ∀ i j k, T1 i j k ⊆ S := fun i j k v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hv⟩⟩⟩)))
  have hS2 : T2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : ∀ v ∉ S, ∀ z : Fv D.host.F v ⊗[D.host.F] D.host.E, z ∈ intLoc D.host.F D.host.E v ↔
      ∀ k, crd B (Fv D.host.F v) z k ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    have h' : v ∉ hbad.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h'
    exact h'
  have hcrd : ∀ z k, crd B (Af D.host.F) (z - algebraMap (Af D.host.F) _ (indS S) * z) k =
      crd B (Af D.host.F) z k - indS S * crd B (Af D.host.F) z k := by
    intro z k
    simp only [crd, ← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · calc g y = g (sPart S y + (y - sPart S y)) := by rw [add_sub_cancel]
      _ = g (sPart S y) := hinv _ _ fun i j k v => ?_
    have e1 : crd B (Af D.host.F) ((y - sPart S y) i j) k v =
        crd B (Af D.host.F) (y i j) k v - indS S v * crd B (Af D.host.F) (y i j) k v := by
      rw [Pi.sub_apply, Pi.sub_apply, sPart, hcrd]
      rfl
    rw [e1, indS_apply]
    by_cases hv : v ∈ S
    · rw [if_pos hv, one_mul, sub_self]
      exact zero_mem _
    · rw [if_neg hv, zero_mul, sub_zero, hPT v fun h' => hv (hS2 h'), mem_intSub, ← crd_projV]
      exact (hS3 v hv _).1 (h v hv i j) k
  · push Not at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    obtain ⟨k, hk⟩ : ∃ k, crd B (Fv D.host.F v) (projV v y i j) k ∉ v.adicCompletionIntegers D.host.F := by
      by_contra hc
      push Not at hc
      exact hij ((hS3 v hv _).2 hc)
    rw [crd_projV] at hk
    refine image_eq_zero_of_notMem_tsupport fun hy => hk ?_
    exact hT1 i j k y hy v fun h' => hv (hS1 i j k h')

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.EvGoodSmul
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7} {a b : ℕ}

def EvGood (Φ : Mx D a b → ℂ) : Prop :=
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ

theorem good_zero (S : Finset (Pl D)) (e : AE D) : Good S e (0 : Mx D a b → ℂ) := by
  intro x
  split_ifs <;> rfl

theorem good_add {S : Finset (Pl D)} {e : AE D} {Φ Ψ : Mx D a b → ℂ} (hΦ : Good S e Φ) (hΨ : Good S e Ψ) :
    Good S e (Φ + Ψ) := by
  intro x
  simp only [Pi.add_apply]
  rw [hΦ x, hΨ x]
  split_ifs with h
  · rfl
  · simp

theorem good_smul {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : Good S e Φ) :
    Good S e (c • Φ) := by
  intro x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hΦ x]
  split_ifs with h
  · rfl
  · simp

theorem evGood_zero : EvGood (0 : Mx D a b → ℂ) :=
  ⟨∅, fun S _ e _ => good_zero S e⟩

theorem evGood_add {Φ Ψ : Mx D a b → ℂ} (hΦ : EvGood Φ) (hΨ : EvGood Ψ) : EvGood (Φ + Ψ) := by
  classical
  obtain ⟨S₁, h₁⟩ := hΦ
  obtain ⟨S₂, h₂⟩ := hΨ
  exact ⟨S₁ ∪ S₂, fun S hS e he =>
    good_add (h₁ S (Finset.union_subset_left hS) e he) (h₂ S (Finset.union_subset_right hS) e he)⟩

theorem evGood_smul {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : EvGood Φ) : EvGood (c • Φ) := by
  obtain ⟨S₀, h⟩ := hΦ
  exact ⟨S₀, fun S hS e he => good_smul c (h S hS e he)⟩

theorem evGood_span {s : Set (Mx D a b → ℂ)} (hs : ∀ φ ∈ s, EvGood φ) :
    ∀ Φ ∈ Submodule.span ℂ s, EvGood Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact evGood_zero
  | add x y _ _ hx hy => exact evGood_add hx hy
  | smul c x _ hx => exact evGood_smul c hx

theorem ev_span {θ : InfFam D} (s : Set (Mx D a b → ℂ)) (hs : schwartzA θ a b = Submodule.span ℂ s)
    (h : ∀ φ ∈ s, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e φ) :
    ∀ Φ ∈ schwartzA θ a b, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ := by
  intro Φ hΦ
  rw [hs] at hΦ
  exact evGood_span h Φ hΦ

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem gen_good {θ : InfFam D} {a b : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e →
      Good S e (fun x : Mx D a b => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) := by
  obtain ⟨S₀, hS₀⟩ := fin_good g hg
  refine ⟨S₀, fun S hS e he x => ?_⟩
  obtain ⟨he1, he2⟩ := he
  obtain ⟨hi1, hi2⟩ := isIdem_eS S
  have heS : e = eS S := ae_ext e (eS S) (fun w => (he1 w).trans (hi1 w).symm)
    (fun v => (he2 v).trans (hi2 v).symm)
  subst heS
  have hinf : ∀ τ (i : Fin a) (j : Fin b), compAt θ τ (eS S • x) i j = compAt θ τ x i j := by
    intro τ i j
    show θ τ (infPart D ((eS S • x) i j)) = θ τ (infPart D (x i j))
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, infPart_eS, one_mul]
  have hfin : (fun (i : Fin a) (j : Fin b) => finPart D ((eS S • x) i j)) =
      sPart S (fun i j => finPart D (x i j)) := by
    funext i j
    show finPart D ((eS S • x) i j) = algebraMap _ _ (indS S) * finPart D (x i j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, finPart_eS]
  simp only [hinf]
  rw [hfin, hS₀ S hS (fun i j => finPart D (x i j))]
  by_cases h : IntOff S x
  · have h' : ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun v hv i j => by
        have := h v hv i j
        rw [cv_eq] at this
        exact this
    rw [if_pos h', if_pos h]
  · have h' : ¬ ∀ v ∉ S, ∀ (i : Fin a) (j : Fin b),
        projV v (fun i j => finPart D (x i j)) i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
      fun h'' => h (fun v hv i j => by
        have := h'' v hv i j
        rw [cv_eq]
        exact this)
    rw [if_neg h', if_neg h, mul_zero]

end PositivityTheory.Rg.Rsw.L.LGoodEv

namespace PositivityTheory.Rg.Rsw.L

theorem goodEv : IdemEx → GoodEv := by
  intro _ D θ _ a b Φ hΦ
  refine LGoodEv.ev_span _ rfl ?_ Φ hΦ
  rintro φ ⟨f, g, hg, rfl⟩
  exact LGoodEv.gen_good f g hg

end PositivityTheory.Rg.Rsw.L

end

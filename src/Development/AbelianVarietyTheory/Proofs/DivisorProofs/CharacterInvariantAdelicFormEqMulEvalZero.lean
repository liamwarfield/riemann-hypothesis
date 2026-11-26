module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulApplyZero
open GlobalTheory.WeilM

noncomputable section

open scoped Classical Topology

namespace GlobalTheory.CharForm

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def cosetInd (U : AddSubgroup X) (q : X ⧸ U) : X → ℂ := fun x => if (x : X ⧸ U) = q then 1 else 0

theorem cosetInd_mem_SB (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X)) (q : X ⧸ U) :
    cosetInd U q ∈ SB X := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  refine ⟨?_, ?_⟩
  · exact (IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous
      QuotientAddGroup.continuous_mk
  · have hK : IsCompact ((fun u => q.out + u) '' (U : Set X)) := hUc.image (continuous_const.add continuous_id)
    have hKc : IsClosed ((fun u => q.out + u) '' (U : Set X)) :=
      (Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)
    refine HasCompactSupport.intro' hK hKc fun x hx => ?_
    simp only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hxq
    apply hx
    refine ⟨-q.out + x, ?_, by simp⟩
    rw [← QuotientAddGroup.out_eq' q] at hxq
    exact QuotientAddGroup.eq.mp hxq.symm

theorem exists_periodic {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose W hWo _ hWN _ using fun x => H _ (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ =>
    ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  have hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X) :=
    Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)
  obtain ⟨U, hUo, hUc, hUN, hUk⟩ := H _ hNm
  refine ⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ W x := Set.mem_iInter₂.mp (hUN hu).2 x hxt
    have h1 : g (x + (y - x)) = g x := hWN x hyx
    have h2 : g (x + (y - x + u)) = g x := hWN x ((W x).add_mem hyx hu')
    rw [add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

theorem apply_eq_of_periodic {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ x : X, g ((x : X ⧸ U).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]; exact hper x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • cosetInd U q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))
  have hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0 := by
    intro q hq
    have hx₀ : q.out ∉ U := by
      intro hm
      apply hq
      rw [← QuotientAddGroup.out_eq' q]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hm
    obtain ⟨χ, hχC, hχU, hχ1⟩ := hUk _ hx₀
    have hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q := by
      funext x
      simp only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs with hxq
      · have hm : -q.out + x ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hxq
          exact QuotientAddGroup.eq.mp hxq.symm
        have := hχU _ hm
        rwa [add_neg_cancel_left] at this
      · rfl
    have e := ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)
    rw [hmul, map_smul, smul_eq_mul] at e
    have : (χ q.out - 1) * a (cosetInd U q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)
  conv_lhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single (0 : X ⧸ U)]
  · rw [map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]
  · intro q _ hq
    rw [map_smul, hkill q hq, smul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self _ _) h

theorem exists_eq_mul_apply_zero : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (C : Set (X → ℂ)),
    (∀ N ∈ nhds (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) →
    ∀ (a : (X → ℂ) →ₗ[ℂ] ℂ), (∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g) →
      ∃ c : ℂ, ∀ g ∈ SB X, a g = c * g 0 := by
  intro X _ _ _ C H a ha
  obtain ⟨U₀, hU₀o, hU₀c, -, hU₀k⟩ := H Set.univ Filter.univ_mem
  refine ⟨a (cosetInd U₀ 0), fun g hg => ?_⟩
  obtain ⟨U, hUo, hUc, hUV, hUk, hper⟩ := exists_periodic H hg (hU₀o.mem_nhds U₀.zero_mem)
  have h1 := apply_eq_of_periodic a ha U hUo hUc hUk hg hper
  have h2 := apply_eq_of_periodic a ha U hUo hUc hUk (cosetInd_mem_SB U₀ hU₀o hU₀c 0) fun x u hu => by
    have : ((u : X) : X ⧸ U₀) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr (hUV hu)
    simp only [cosetInd, QuotientAddGroup.mk_add, this, add_zero]
  have h0 : cosetInd U₀ (0 : X ⧸ U₀) 0 = 1 := by simp [cosetInd]
  rw [h0, one_mul] at h2
  rw [h1, h2, mul_comm]

end GlobalTheory.CharForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.CharInvForm

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1]⟩

theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.SchwartzDiv.hadamard V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.CharFormDeriv.charForm_kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b :=
  Prod.ext (zero_add (0 : Ainf F)).symm rfl

theorem dot_pairA_fin {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Af F) :
    (x ⬝ᵥ fun i => pairA F 0 (y i)) = pairA F 0 ((fun i => (x i).2) ⬝ᵥ y) := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.fst (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = (fun i => (x i).2) ⬝ᵥ y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    rfl
  exact Prod.ext h1 h2

theorem dot_pairA_inf {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Ainf F) :
    (x ⬝ᵥ fun i => pairA F (y i) 0) = pairA F (∑ i, (x i).1 * y i) 0 := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = ∑ i, (x i).1 * y i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    rfl
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.snd (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  exact Prod.ext h1 h2

theorem mem_schA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f g 0 = f 0 * g 0 := by
  simp only [pureA]
  congr 2
  · funext i
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

theorem psi_dot_inf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (x : κ → AF F) (Y : κ → mixedEmbedding.mixedSpace F) :
    ψ (x ⬝ᵥ fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) =
      Complex.exp (Complex.I * ((-(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) i * Y i) : ℝ) : ℂ)) := by
  have hat : At (evI F) (pairA F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    show (u.1 * _, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
    rw [h1, zero_mul, mul_zero]
  rw [dot_pairA_inf, hψ.2.2 _ hat]
  show Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i))) : ℝ) : ℂ)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [map_mul, RingEquiv.apply_symm_apply]
  congr 1
  push_cast
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ →
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hl hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    obtain ⟨T, hT⟩ := hl g hg
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY, mul_assoc])
    exact ⟨α, fun f => (hT f).trans (hα f)⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add (f := _)]
        congr 1
        funext x
        simp [pureA, mul_add]
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp [pureA, mul_comm, mul_assoc] }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp [pureA, dot_pairA_fin, mul_left_comm])
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add (f := _), h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

end GlobalTheory.CharInvForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ → (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  first | exact @GlobalTheory.CharInvForm.main | exact GlobalTheory.CharInvForm.main | (intros; apply GlobalTheory.CharInvForm.main <;> assumption)
end

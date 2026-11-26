module

public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentExtNorm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DifferentLatIndex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

def DifferentLatIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K]
    (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (diffLat s I).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatStep
section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DiffLatFree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section IdealLat

variable {F : Type} [Field F] [NumberField F] {N ρ : ℕ}

def idealLat (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) : Submodule (𝓞 F) (Fin N → F) :=
  Submodule.map (Fintype.linearCombination (𝓞 F) w) (Submodule.pi Set.univ fun _ => a)

theorem linearCombination_injective {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) :
    Function.Injective (Fintype.linearCombination (𝓞 F) w) := by
  have hw' : LinearIndependent (𝓞 F) w := (LinearIndependent.iff_fractionRing (𝓞 F) F).2 hw
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext i
  exact Fintype.linearIndependent_iff.1 hw' c (by rwa [Fintype.linearCombination_apply] at hc) i

omit [NumberField F] in
theorem idealLat_toAddSubgroup (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) :
    (idealLat w a).toAddSubgroup = AddSubgroup.map (Fintype.linearCombination (𝓞 F) w).toAddMonoidHom
      (AddSubgroup.pi Set.univ fun _ => a.toAddSubgroup) := by
  ext x
  simp [idealLat, Submodule.mem_pi, AddSubgroup.mem_pi]

theorem idealLat_relIndex {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) {a b : Ideal (𝓞 F)}
    (hab : a ≤ b) :
    (idealLat w a).toAddSubgroup.relIndex (idealLat w b).toAddSubgroup * Ideal.absNorm b ^ ρ =
      Ideal.absNorm a ^ ρ := by
  rw [idealLat_toAddSubgroup, idealLat_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (linearCombination_injective hw)]
  have h := AddSubgroup.relIndex_mul_index (H := AddSubgroup.pi Set.univ fun _ : Fin ρ => a.toAddSubgroup)
    (K := AddSubgroup.pi Set.univ fun _ : Fin ρ => b.toAddSubgroup) (fun x hx i hi => hab (hx i hi))
  rw [AddSubgroup.index_pi, AddSubgroup.index_pi] at h
  simpa [Ideal.absNorm_eq_index] using h


omit [NumberField F] in
theorem idealLat_smul (w : Fin ρ → Fin N → F) (r : 𝓞 F) (a : Ideal (𝓞 F)) :
    idealLat (fun i => r • w i) a = idealLat w (Ideal.span {r} * a) := by
  ext x
  simp only [idealLat, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => r * c i, fun i => Ideal.mem_span_singleton_mul.2 ⟨c i, hc i, rfl⟩, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    choose d hd hdc using fun i => Ideal.mem_span_singleton_mul.1 (hc i)
    refine ⟨d, hd, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← hdc i, smul_smul, mul_comm]


omit [NumberField F] in
theorem idealLat_top (w : Fin ρ → Fin N → F) :
    idealLat w ⊤ = Submodule.span (𝓞 F) (Set.range w) := by
  rw [idealLat, Submodule.pi_top, Submodule.map_top, Fintype.range_linearCombination]

end IdealLat

section DiffLatSpan

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N ρ : ℕ}


omit [NumberField K] in
theorem diffLat_mono (s : Em →+* K) {M M' : Submodule (𝓞 Em) (Fin N → Em)} (h : M ≤ M') :
    diffLat s M ≤ diffLat s M' :=
  Submodule.span_mono (Set.image_mono fun _ ⟨x, hx, y, hy, hu⟩ => ⟨x, hx, y, h hy, hu⟩)

theorem diffLat_span (s : Em →+* K) (w : Fin ρ → Fin N → Em) :
    diffLat s (Submodule.span (𝓞 Em) (Set.range w)) = idealLat (fun a i => s (w a i)) (extDifferent s) := by
  apply le_antisymm
  · rw [diffLat, Submodule.span_le]
    rintro _ ⟨u, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 hy
    refine ⟨fun a => RingOfIntegers.mapRingHom s (x * c a),
      fun a _ => Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ hx), ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Fintype.linearCombination_apply, Finset.sum_apply, map_sum, Algebra.smul_def, mul_assoc,
      Finset.mul_sum]
  · rw [idealLat, Submodule.map_le_iff_le_comap]
    intro c hc
    simp only [Submodule.mem_comap, Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    have key : extDifferent s ≤ (diffLat s (Submodule.span (𝓞 Em) (Set.range w))).comap
        (LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (w a i))) := by
      rw [extDifferent, Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(x : Em) • w a, ⟨x, hx, w a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
    exact key (hc a (Set.mem_univ a))

end DiffLatSpan

end GroundTheory.Heights₂.Heights.NineStatements
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section Step

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N : ℕ}

theorem absNorm_map_mapRingHom (s : Em →+* K) (b : Ideal (𝓞 Em)) :
    letI : Algebra Em K := s.toAlgebra
    Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) = Ideal.absNorm b ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  have h1 : RingOfIntegers.mapRingHom s = algebraMap (𝓞 Em) (𝓞 K) := rfl
  have h3 : Module.finrank (𝓞 Em) (𝓞 K) = Module.finrank Em K :=
    (IsFractionRing.finrank_eq (𝓞 Em) Em (𝓞 K) K).symm
  rw [h1, Ideal.absNorm_algebraMap, h3]


omit [NumberField Em] in
theorem span_singleton_toAddSubgroup (x : Fin N → Em) :
    (Submodule.span (𝓞 Em) {x}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 Em)).map (LinearMap.toSpanSingleton (𝓞 Em) _ x).toAddMonoidHom := by
  ext y
  simp [Submodule.mem_span_singleton]

omit [NumberField K] in
theorem map_toAddSubgroup' (f : 𝓞 K →ₗ[𝓞 K] (Fin N → K)) (D : Ideal (𝓞 K)) :
    (Submodule.map f D).toAddSubgroup = D.toAddSubgroup.map f.toAddMonoidHom := by
  ext y
  simp

theorem relIndex_mul_ideal {F : Type} [Field F] [NumberField F] (D B : Ideal (𝓞 F)) (hD : Ideal.absNorm D ≠ 0) :
    (D * B).toAddSubgroup.relIndex D.toAddSubgroup = Ideal.absNorm B := by
  have h := AddSubgroup.relIndex_mul_index (H := (D * B).toAddSubgroup) (K := D.toAddSubgroup)
    (Submodule.toAddSubgroup_mono Ideal.mul_le_left)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, map_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD) (by rw [h, mul_comm])

theorem diffLat_step (s : Em →+* K) (P : Submodule (𝓞 Em) (Fin N → Em)) (x : Fin N → Em)
    (hP : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup ≤
      P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ^ Module.finrank Em K := by
  let _ : Algebra Em K := s.toAlgebra
  let g : 𝓞 Em →ₗ[𝓞 Em] (Fin N → Em) := LinearMap.toSpanSingleton (𝓞 Em) _ x
  let f : 𝓞 K →ₗ[𝓞 K] (Fin N → K) := LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (x i))
  let b : Ideal (𝓞 Em) := P.comap g
  have hPQ : P.toAddSubgroup.relIndex (P ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup = Ideal.absNorm b := by
    rw [Submodule.sup_toAddSubgroup, span_singleton_toAddSubgroup, AddSubgroup.relIndex_sup_left,
      ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, Ideal.absNorm_eq_index]
    rfl
  have hXQ : diffLat s (P ⊔ Submodule.span (𝓞 Em) {x}) =
      diffLat s P ⊔ Submodule.map f (extDifferent s) := by
    apply le_antisymm
    · rw [diffLat, Submodule.span_le]
      rintro _ ⟨u, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
      have e : (fun i => s (((y : Em) • (p + c • x)) i)) =
          (fun i => s (((y : Em) • p) i)) + f (RingOfIntegers.mapRingHom s (y * c)) := by
        funext i
        simp [f, Algebra.smul_def, mul_add, mul_assoc]
      show (fun i => s (((y : Em) • (p + c • x)) i)) ∈ _
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, ⟨y, hy, p, hp, rfl⟩, rfl⟩)
        (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_right c _ hy)))
    · refine sup_le (diffLat_mono s le_sup_left) ?_
      rw [Submodule.map_le_iff_le_comap, extDifferent, Ideal.map_le_iff_le_comap]
      intro y hy
      simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(y : Em) • x, ⟨y, hy, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
  have h1 : (diffLat s P).toAddSubgroup.relIndex (diffLat s (P ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup =
      ((diffLat s P).toAddSubgroup.comap f.toAddMonoidHom).relIndex (extDifferent s).toAddSubgroup := by
    rw [hXQ, Submodule.sup_toAddSubgroup, map_toAddSubgroup', AddSubgroup.relIndex_sup_left,
      AddSubgroup.relIndex_comap]
  have h2 : extDifferent s * b.map (RingOfIntegers.mapRingHom s) ≤ (diffLat s P).comap f := by
    rw [extDifferent, ← Ideal.map_mul, Ideal.map_le_iff_le_comap]
    refine Ideal.mul_le.2 fun y hy c hc => ?_
    have hc' : c • x ∈ P := hc
    simp only [Ideal.mem_comap, Submodule.mem_comap, f, LinearMap.toSpanSingleton_apply]
    apply Submodule.subset_span
    refine ⟨(y : Em) • (c • x), ⟨y, hy, c • x, hc', rfl⟩, ?_⟩
    funext i
    simp [Algebra.smul_def, mul_assoc]
  have hD : Ideal.absNorm (extDifferent s) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact extDifferent_ne_bot s
  have h3 : (extDifferent s * b.map (RingOfIntegers.mapRingHom s)).toAddSubgroup.relIndex
      (extDifferent s).toAddSubgroup = Ideal.absNorm (b.map (RingOfIntegers.mapRingHom s)) := by
    exact relIndex_mul_ideal _ _ hD
  have h4 := absNorm_map_mapRingHom s b
  rw [h1, hPQ, ← h4, ← h3]
  refine AddSubgroup.relIndex_le_of_le_left (fun z hz => h2 hz) ?_
  rw [h3, h4]
  exact pow_ne_zero _ (hPQ ▸ hP)

theorem diffLat_relIndex_le (s : Em →+* K) {M' M : Submodule (𝓞 Em) (Fin N → Em)} (hle : M' ≤ M) (hfg : M.FG)
    (hM : M'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    letI : Algebra Em K := s.toAlgebra
    (diffLat s M').toAddSubgroup.relIndex (diffLat s M).toAddSubgroup ≤
      M'.toAddSubgroup.relIndex M.toAddSubgroup ^ Module.finrank Em K := by
  classical
  let _ : Algebra Em K := s.toAlgebra
  obtain ⟨T, hT⟩ := hfg
  have hTM : (↑T : Set (Fin N → Em)) ⊆ M := hT ▸ Submodule.subset_span
  have key : ∀ T : Finset (Fin N → Em), (↑T : Set (Fin N → Em)) ⊆ M →
      (diffLat s M').toAddSubgroup.relIndex (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup ≤
        M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup ^ Module.finrank Em K := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert x T hx ih =>
      intro hT'
      have hxM : x ∈ M := hT' (Finset.mem_insert_self _ _)
      have hTM' : (↑T : Set (Fin N → Em)) ⊆ M := fun y hy => hT' (Finset.mem_insert_of_mem hy)
      have hPeq : M' ⊔ Submodule.span (𝓞 Em) ↑(insert x T) =
          (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} := by
        rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span (𝓞 Em) {x}), ← sup_assoc]
      rw [hPeq]
      have hP_le : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ M := sup_le hle (Submodule.span_le.2 hTM')
      have hPx_le : (M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x} ≤ M :=
        sup_le hP_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hxM))
      have hne : M'.toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hM (AddSubgroup.relIndex_eq_zero_of_le_right hPx_le h)
      have hmul := AddSubgroup.relIndex_mul_relIndex M'.toAddSubgroup
        (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup
        ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup
        (le_sup_left : M' ≤ _) (le_sup_left : M' ⊔ Submodule.span (𝓞 Em) ↑T ≤ _)
      have hstep : (M' ⊔ Submodule.span (𝓞 Em) ↑T).toAddSubgroup.relIndex
          ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x}).toAddSubgroup ≠ 0 :=
        fun h => hne (by rw [← hmul, h, mul_zero])
      have hX := AddSubgroup.relIndex_mul_relIndex (diffLat s M').toAddSubgroup
        (diffLat s (M' ⊔ Submodule.span (𝓞 Em) ↑T)).toAddSubgroup
        (diffLat s ((M' ⊔ Submodule.span (𝓞 Em) ↑T) ⊔ Submodule.span (𝓞 Em) {x})).toAddSubgroup
        (diffLat_mono s le_sup_left) (diffLat_mono s le_sup_left)
      rw [← hX, ← hmul, mul_pow]
      exact Nat.mul_le_mul (ih hTM') (diffLat_step s _ x hstep)
  have hM_eq : M = M' ⊔ Submodule.span (𝓞 Em) ↑T := by rw [hT, sup_eq_right.2 (hT ▸ hle)]
  rw [hM_eq] at hM ⊢
  exact key T hTM

end Step

end GroundTheory.Heights₂.Heights.NineStatements
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PTorusIndex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

theorem fg_of_isNzFamily {Em : Type} [Field Em] [NumberField Em] {N : ℕ} {I : Submodule (𝓞 Em) (Fin N → Em)}
    {ρ : ℕ} {v : Fin ρ → Fin N → Em} (hv : IsNzFamily I ρ v) : I.FG := by
  set J := Submodule.span (𝓞 Em) (Set.range v) with hJdef
  have hJ : J.FG := Submodule.fg_span (Set.finite_range v)
  set m := J.toAddSubgroup.relIndex I.toAddSubgroup with hmdef
  have hm : m ≠ 0 := hv.2.2.2
  have hmem : ∀ u ∈ I, m • u ∈ J := by
    intro u hu
    have h := AddSubgroup.nsmul_index_mem (J.toAddSubgroup.addSubgroupOf I.toAddSubgroup) ⟨u, hu⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    exact h
  have : IsNoetherian (𝓞 Em) J := isNoetherian_of_fg_of_noetherian J hJ
  let f : I →ₗ[𝓞 Em] J :=
    { toFun := fun u => ⟨m • (u : Fin N → Em), hmem u u.2⟩
      map_add' := fun a b => by ext1; simp [smul_add]
      map_smul' := fun c a => by ext1; simp [smul_comm] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : m • (a : Fin N → Em) = m • (b : Fin N → Em) := congrArg Subtype.val hab
    rw [← Nat.cast_smul_eq_nsmul Em, ← Nat.cast_smul_eq_nsmul Em] at h1
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hm) h1)
  exact (Submodule.fg_top I).1 (fg_of_injective (N := ⊤) f hf)

theorem TorusIndex.proof (hA : EigenLatDifferent.Statement) (hB : DifferentLatIndex.Statement) :
    TorusIndex.Statement := by
  intro Em _ _ K _ _ ι hι N I ρ v hv s
  rw [hA Em K ι hι N I (fg_of_isNzFamily hv) s]
  exact hB Em K N I ρ v hv s

end GroundTheory.Heights₂.Heights.NineStatements
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

theorem genIndex_eq_of_le {G : Type*} [AddCommGroup G] {W P Q : AddSubgroup G} (hWP : W ≤ P) (hWQ : W ≤ Q)
    (hQ : W.relIndex Q ≠ 0) : genIndex P Q = (W.relIndex P : ℝ) / (W.relIndex Q) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex W (P ⊓ Q) P (le_inf hWP hWQ) inf_le_left
  have h2 := AddSubgroup.relIndex_mul_relIndex W (P ⊓ Q) Q (le_inf hWP hWQ) inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at h1
  rw [AddSubgroup.inf_relIndex_right] at h2
  have ht : W.relIndex (P ⊓ Q) ≠ 0 := fun h => hQ (by rw [← h2, h, zero_mul])
  rw [genIndex, ← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left]
  exact_mod_cast ht

theorem DifferentLatIndex.proof : DifferentLatIndex.Statement := by
  intro Em _ _ K _ _ N I ρ v hv s
  let _ : Algebra Em K := s.toAlgebra
  have hIfg : I.FG := fg_of_isNzFamily hv
  obtain ⟨_, hvI, hli, hm⟩ := hv
  set J0 := Submodule.span (𝓞 Em) (Set.range v) with hJ0
  set m := familyIndex I v with hmdef
  have hm' : J0.toAddSubgroup.relIndex I.toAddSubgroup = m := rfl
  rw [hm'] at hm
  set e := Module.finrank Em K with he
  have hdeg : Module.finrank ℚ K = Module.finrank ℚ Em * e := (Module.finrank_mul_finrank ℚ Em K).symm
  have hnE : Module.finrank ℚ Em ≠ 0 := Module.finrank_pos.ne'

  have hE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).1 hli
  have hmE : (m : Em) ≠ 0 := by exact_mod_cast hm
  let w : Fin ρ → Fin N → Em := fun a => (m : Em)⁻¹ • v a
  have hw : LinearIndependent Em w :=
    hE.units_smul (fun _ => Units.mk0 ((m : Em)⁻¹) (inv_ne_zero hmE))
  have hvK : LinearIndependent K (fun a i => s (v a i)) :=
    (linearIndependent_algebraMap_comp_iff (R := Em) (S := K)).2 hE
  have hwK : LinearIndependent K (fun a i => s (w a i)) :=
    (linearIndependent_algebraMap_comp_iff (R := Em) (S := K)).2 hw

  have hvw : v = fun a => (m : 𝓞 Em) • w a := by
    funext a i
    simp [w, Algebra.smul_def, hmE]
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm
  have hsvw : (fun a i => s (v a i)) = fun a => (m : 𝓞 K) • fun i => s (w a i) := by
    funext a i
    simp [w, Algebra.smul_def, hmK]
  set B := Submodule.span (𝓞 Em) (Set.range w) with hB
  have hJ0_eq : J0 = idealLat w (Ideal.span {(m : 𝓞 Em)}) := by
    rw [hJ0, ← idealLat_top, hvw, idealLat_smul, Ideal.mul_top]
  have hB_eq : B = idealLat w ⊤ := (idealLat_top w).symm
  have hXJ0 : diffLat s J0 = idealLat (fun a i => s (v a i)) (extDifferent s) := diffLat_span s v
  have hXJ0' : diffLat s J0 = idealLat (fun a i => s (w a i)) (Ideal.span {(m : 𝓞 K)} * extDifferent s) := by
    rw [hXJ0, hsvw, idealLat_smul]
  have hXB : diffLat s B = idealLat (fun a i => s (w a i)) (extDifferent s) := diffLat_span s w
  have hF : familyLat s v = idealLat (fun a i => s (v a i)) ⊤ := (idealLat_top _).symm

  have hD : Ideal.absNorm (extDifferent s) = (discr Em).natAbs ^ e := absNorm_extDifferent s
  have hDne : Ideal.absNorm (extDifferent s) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact extDifferent_ne_bot s
  have iF : (diffLat s J0).toAddSubgroup.relIndex (familyLat s v).toAddSubgroup =
      Ideal.absNorm (extDifferent s) ^ ρ := by
    have h := idealLat_relIndex hvK (le_top : extDifferent s ≤ ⊤)
    rw [Ideal.absNorm_top, one_pow, mul_one] at h
    rw [hXJ0, hF, h]
  have iB : J0.toAddSubgroup.relIndex B.toAddSubgroup = (m ^ Module.finrank ℚ Em) ^ ρ := by
    have h := idealLat_relIndex hw (le_top : Ideal.span {(m : 𝓞 Em)} ≤ ⊤)
    rw [Ideal.absNorm_top, one_pow, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h
    rw [hJ0_eq, hB_eq, h]
  have iXB : (diffLat s J0).toAddSubgroup.relIndex (diffLat s B).toAddSubgroup =
      (m ^ Module.finrank ℚ K) ^ ρ := by
    have h := idealLat_relIndex hwK (Ideal.mul_le_right : Ideal.span {(m : 𝓞 K)} * extDifferent s ≤ extDifferent s)
    rw [map_mul, mul_pow, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h
    rw [hXJ0', hXB]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hDne) ρ) h

  have hJ0I : J0 ≤ I := Submodule.span_le.2 (Set.range_subset_iff.2 hvI)
  have hIB : I ≤ B := by
    intro u hu
    have hmu : m • u ∈ J0 := by
      have h := AddSubgroup.nsmul_index_mem (J0.toAddSubgroup.addSubgroupOf I.toAddSubgroup) ⟨u, hu⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h
      exact h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 hmu
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).2 ⟨c, ?_⟩
    have : ∑ a, c a • w a = (m : Em)⁻¹ • ∑ a, c a • v a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [w]
      rw [smul_comm]
    rw [this, hc, ← Nat.cast_smul_eq_nsmul Em, inv_smul_smul₀ hmE]
  have hBfg : B.FG := Submodule.fg_span (Set.finite_range w)

  have hmulB := AddSubgroup.relIndex_mul_relIndex J0.toAddSubgroup I.toAddSubgroup B.toAddSubgroup hJ0I hIB
  have hmulX := AddSubgroup.relIndex_mul_relIndex (diffLat s J0).toAddSubgroup (diffLat s I).toAddSubgroup
    (diffLat s B).toAddSubgroup (diffLat_mono s hJ0I) (diffLat_mono s hIB)
  have hIBne : I.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, mul_zero, iB] at hmulB
    exact pow_ne_zero _ (pow_ne_zero _ hm) hmulB.symm
  have hX1 := diffLat_relIndex_le s hJ0I hIfg (by rw [hm']; exact hm)
  have hX2 := diffLat_relIndex_le s hIB hBfg hIBne
  change _ ≤ _ ^ e at hX1 hX2
  have hprod : (diffLat s J0).toAddSubgroup.relIndex (diffLat s I).toAddSubgroup *
      (diffLat s I).toAddSubgroup.relIndex (diffLat s B).toAddSubgroup =
      (J0.toAddSubgroup.relIndex I.toAddSubgroup) ^ e * (I.toAddSubgroup.relIndex B.toAddSubgroup) ^ e := by
    rw [hmulX, iXB, ← mul_pow, hmulB, iB, hdeg, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hBpos : 0 < (I.toAddSubgroup.relIndex B.toAddSubgroup) ^ e := pow_pos (Nat.pos_of_ne_zero hIBne) e
  have iXI : (diffLat s J0).toAddSubgroup.relIndex (diffLat s I).toAddSubgroup = m ^ e := by
    rw [← hm']
    rcases lt_or_eq_of_le hX1 with hlt | heq
    · exact absurd hprod (ne_of_lt (Nat.mul_lt_mul_of_lt_of_le hlt hX2 hBpos))
    · exact heq

  have hWQ : diffLat s J0 ≤ familyLat s v := by
    rw [hXJ0, hF]
    exact Submodule.map_mono (fun c _ => Submodule.mem_pi.2 fun i _ => Submodule.mem_top)
  rw [genIndex_eq_of_le (diffLat_mono s hJ0I) hWQ (by rw [iF]; exact pow_ne_zero _ hDne), iXI, iF, hD]
  have hexp : (Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em = (e : ℝ) := by
    rw [hdeg, Nat.cast_mul]
    field_simp
  rw [hexp, Real.rpow_natCast, div_pow]
  have habs : ((discr Em).natAbs : ℝ) = |(discr Em : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [habs]
  ring

end GroundTheory.Heights₂.Heights.NineStatements

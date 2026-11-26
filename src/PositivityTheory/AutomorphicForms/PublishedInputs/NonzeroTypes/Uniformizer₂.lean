module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Uniformizer₂
noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetImage
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDUnit
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace P_DUnit

theorem isUnit_det_sub (A : GL (Fin n) 𝒪[k]) (a : Fin G.s)
    (hA : ∀ i j, G.bl j < G.bl i → (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
      (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  set M := (IsLocalRing.residue 𝒪[k]).mapMatrix (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hdet : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact (Matrix.isUnits_det_units A).map _
  have htri := Matrix.twoBlockTriangular_det M (fun i => G.bl i ≤ a) (fun i hi j hj => by
    rw [hM, RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff]
    exact hA i j (lt_of_le_of_lt hj (not_le.1 hi)))
  rw [htri] at hdet
  have h1 := isUnit_of_mul_isUnit_left hdet
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  exact h1.ne_zero

end P_DUnit

theorem step_DUnit : ModulusOnUnitsProp G := by
  intro hb g hg a
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hg.1
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hA : ∀ i j, G.bl j < G.bl i →
      (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j hij
    obtain ⟨y, hy, hyx⟩ := hg.2 i j hij
    have hc : cc G.μ (G.bl j) (G.bl i) ≠ 0 := by
      have := hb.1 (G.bl j) (G.bl i) (ne_of_lt hij)
      omega
    have : y = (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j := hinj (by rw [hyx]; rfl)
    rw [← this]
    exact Ideal.pow_le_self hc hy
  have hu := P_DUnit.isUnit_det_sub G A a hA
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  rfl

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PKill
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_kill

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem PJ_smul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (a : ℂ) (v : V) : G.PJ π r (a • v) = a • G.PJ π r v := by
  unfold Grp.PJ
  rw [smul_finsum]
  congr 1
  funext c
  rw [map_smul, smul_comm]

theorem core_mul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hmul : ∀ v : V, (∀ u ∈ KC k n r, π u v = v) → ∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v)
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 := by
  obtain ⟨j, hjJ, hyj, hne⟩ := hj
  have hx' : ∀ g ∈ G.JSet, π g x = G.lam g • x := hx
  have hjw : π j (π y x) = G.lam (y⁻¹ * j * y) • π y x := by
    have e : j * y = y * (y⁻¹ * j * y) := by group
    have e1 : π j (π y x) = π (j * y) x := by rw [map_mul]; rfl
    have e2 : π (y * (y⁻¹ * j * y)) x = π y (π (y⁻¹ * j * y) x) := by rw [map_mul]; rfl
    rw [e1, e, e2, hx' _ hyj, map_smul]
  have key := hmul (π y x) hfix j hjJ
  rw [hjw, PJ_smul] at key
  have h0 : (G.lam (y⁻¹ * j * y) - G.lam j) • G.PJ π r (π y x) = 0 := by
    rw [sub_smul, key, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hPJ : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
      ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
        G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
        (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v))
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 :=
  core_mul G π r (fun v hv => (hPJ.2 v hv).2.1) x hx y hfix hj

end UpperTheory.TNZ.Grp.P_kill

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem step_kill : G.AnnihilationProp := by
  intro hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 hPJ V _ _ π r hr x hx y hfix hj
  exact P_kill.core G π r (hPJ hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 V π r hr) x hx y hfix hj

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LeviEigenvectorMembership
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.LeviEigenvectorMembership

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

theorem mem_left_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {g : GL (Fin n) k} (hg : g ∈ G.JSet) (h : GL (Fin n) k) : g * h ∈ G.JSet ↔ h ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hh => hmul g hg h hh⟩
  have := hmul _ (hinv g hg) _ hgh
  simpa [← mul_assoc] using this

theorem mem_right_iff (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet) (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    {h : GL (Fin n) k} (hh : h ∈ G.JSet) (g : GL (Fin n) k) : g * h ∈ G.JSet ↔ g ∈ G.JSet := by
  refine ⟨fun hgh => ?_, fun hg => hmul g hg h hh⟩
  have := hmul _ hgh _ (hinv h hh)
  simpa [mul_assoc] using this

theorem levi_eigenvector_of_conditions (hcb : CompactConductorBasicProp (k := k)) (hccB : CompactConductorBoundProp G) (hΔU : ModulusOnUnitsProp G) (hΔM : ModulusMultiplicativeProp G)
    (hJone : JacquetOneProp G) (hJmul : JacquetMultiplicativeProp G) (hJinv : JacquetInverseProp G) (hlM : LambdaMultiplicativeProp G)
    (hlB : LambdaBasicProp G) (hKC : CompactOpenKernelProp G) :
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧ ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet →
      Rreg (k := k) (n := n) j G.v0 = G.lam j • G.v0 := by
  have hmul := hJmul hcb hccB
  have hinv := hJinv hcb hccB
  have hlam := hlM hcb hΔU hΔM hccB
  obtain ⟨hl1, -, hlK⟩ := hlB hccB
  have hKJ : KC k n G.lev ⊆ G.JSet := (hKC hccB G.lev).2.2.2.2 le_rfl

  have hright : ∀ (g j : ↥(KO k (Fin n))), (j : GL (Fin n) k) ∈ G.JSet →
      G.v0 (g * j) = G.lam j * G.v0 g := by
    intro g j hj
    simp only [Grp.v0, Subgroup.coe_mul, mem_right_iff G hmul hinv hj]
    split_ifs with hg
    · rw [hlam _ hg _ hj, mul_comm]
    · simp
  refine ⟨⟨fun p hp g => ?_, fun g u hu => ?_⟩, ?_, fun j hj => ?_⟩
  · have hpJ : (p : GL (Fin n) k) ∈ G.JSet := hJone.2 hp
    simp only [Grp.v0, Subgroup.coe_mul, mem_left_iff G hmul hinv hpJ]
    split_ifs with hg
    · rw [hlam _ hpJ _ hg]
    · simp
  · rw [hright g u (hKJ hu), hlK _ hu, one_mul]
  · intro h0
    have := congrFun h0 1
    simp only [Grp.v0, OneMemClass.coe_one, if_pos hJone.1, hl1, Pi.zero_apply] at this
    exact one_ne_zero this
  · funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hright g j hj]
    rfl

end UpperTheory.TNZ.Grp.LeviEigenvectorMembership

namespace UpperTheory.TNZ.Grp

theorem leviEigenvector_holds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : NonzeroLeviEigenvectorExists G :=
  fun hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC =>
    LeviEigenvectorMembership.levi_eigenvector_of_conditions G hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.P_Jmul
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_Jmul

theorem inPow_zero_of_KO {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) :
    InPow 0 ((g : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨g', rfl⟩ := hg
  exact ⟨(g' : Matrix (Fin n) (Fin n) 𝒪[k]) i j, by simp, rfl⟩

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem inPow_mul {a b : ℕ} {x y : k} (hx : InPow a x) (hy : InPow b y) : InPow (a + b) (x * y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', map_mul _ _ _⟩

theorem inPow_add {a : ℕ} {x y : k} (hx : InPow a x) (hy : InPow a y) : InPow a (x + y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩

theorem inPow_zero (a : ℕ) : InPow a (0 : k) := ⟨0, zero_mem _, map_zero _⟩

theorem inPow_sum {a : ℕ} {ι : Type} (s : Finset ι) (f : ι → k) (h : ∀ i ∈ s, InPow a (f i)) :
    InPow a (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using inPow_zero (k := k) a
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact inPow_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

end P_Jmul

theorem step_Jmul {n : ℕ} (G : Grp k n) : JacquetMultiplicativeProp G := by
  intro hcc0 hcb g hg h hh
  have hcc := fun a b c => hcc0 G.s G.μ (fun a b => ⟨cc G.μ a b, hcb.2.2.2 a b⟩) a b c
  simp only [Grp.JSet, Set.mem_ofPred_eq] at hg hh ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨mul_mem hg1 hh1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine P_Jmul.inPow_sum _ _ fun l _ => ?_
  rcases le_or_gt (G.bl l) (G.bl j) with hl | hl
  · have hp := P_Jmul.inPow_mul (hg2 i l (lt_of_le_of_lt hl hij)) (P_Jmul.inPow_zero_of_KO hh1 l j)
    rw [add_zero] at hp
    exact P_Jmul.inPow_mono (G.ball _ _ _ _ hl hij le_rfl) hp
  rcases le_or_gt (G.bl i) (G.bl l) with hl' | hl'
  · have hp := P_Jmul.inPow_mul (P_Jmul.inPow_zero_of_KO hg1 i l) (hh2 l j (lt_of_lt_of_le hij hl'))
    rw [zero_add] at hp
    exact P_Jmul.inPow_mono (G.ball _ _ _ _ le_rfl hij hl') hp
  · have hp := P_Jmul.inPow_mul (hg2 i l hl') (hh2 l j hl)
    refine P_Jmul.inPow_mono ?_ hp
    exact le_trans (hcc (G.bl j) (G.bl l) (G.bl i)).2.2
      (max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _))

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.StepV0Stable
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_V0stable

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem alg_inj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_apply {n : ℕ} (A : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := rfl

theorem conj_mem_KC {n r : ℕ} (g u : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) (hu : u ∈ KC k n r) :
    g⁻¹ * u * g ∈ KC k n r := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨⟨B, rfl⟩, hB⟩ := hu
  have hB' : ∀ i j, (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hB i j
    have hyeq : y = (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
      apply alg_inj
      rw [hyx, coe_map_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    exact hyeq ▸ hy
  have key : ∀ i j, ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j
      - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    have h : ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) - 1
        = ((A⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k])
          * ((B : Matrix (Fin n) (Fin n) 𝒪[k]) - 1) * (A : Matrix (Fin n) (Fin n) 𝒪[k]) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [← Matrix.sub_apply, h, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.sub_apply]
    exact hB' m l
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨_, rfl⟩, fun i j => ⟨_, key i j, ?_⟩⟩
  rw [coe_map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

end P_V0stable

theorem step_V0stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : FixedSubspaceStableProp G := by
  intro _ _ g φ hφ
  obtain ⟨h1, h2⟩ : (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO → ∀ x, φ (p * x) = G.lam p * φ x) ∧
      ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev → φ (x * u) = φ x := hφ
  show (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO →
      ∀ x, Rreg (k := k) (n := n) g φ (p * x) = G.lam p * Rreg (k := k) (n := n) g φ x) ∧
    ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev →
      Rreg (k := k) (n := n) g φ (x * u) = Rreg (k := k) (n := n) g φ x
  refine ⟨fun p hp x => ?_, fun x u hu => ?_⟩
  · show φ (p * x * g) = G.lam p * φ (x * g)
    rw [mul_assoc]
    exact h1 p hp (x * g)
  · show φ (x * u * g) = φ (x * g)
    have hc : ((g⁻¹ * u * g : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n G.lev := by
      change ((g : GL (Fin n) k))⁻¹ * (u : GL (Fin n) k) * (g : GL (Fin n) k) ∈ KC k n G.lev
      exact P_V0stable.conj_mem_KC _ _ g.2 hu
    have e : x * u * g = x * g * (g⁻¹ * u * g) := by group
    rw [e]
    exact h2 _ _ hc

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamMul
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_lamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chk_mul (ψ : kˣ →* ℂˣ) {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    chk ψ (x * y) = chk ψ x * chk ψ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  unfold chk
  rw [dite_eq_right hxy, dite_eq_right hx, dite_eq_right hy]
  have e : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
  rw [e, map_mul, Units.val_mul]

theorem algebraMap_unit_ne_zero (u : 𝒪[k]ˣ) : algebraMap 𝒪[k] k (u : 𝒪[k]) ≠ 0 :=
  (u.isUnit.map (algebraMap 𝒪[k] k)).ne_zero

theorem chk_unit (ψ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) :
    chk ψ (algebraMap 𝒪[k] k (u : 𝒪[k])) = ((res ψ u : ℂˣ) : ℂ) := by
  unfold chk
  rw [dite_eq_right (algebraMap_unit_ne_zero u)]
  have e : Units.mk0 (algebraMap 𝒪[k] k (u : 𝒪[k])) (algebraMap_unit_ne_zero u) = unitIncl k u :=
    Units.ext rfl
  rw [e]
  rfl

variable {n : ℕ} (G : Grp k n)

theorem Δ_ne_zero (hU : ModulusOnUnitsProp G) (hB : CompactConductorBoundProp G) {g : GL (Fin n) k} (hg : g ∈ G.JSet)
    (a : Fin G.s) : G.Δ a g ≠ 0 := by
  obtain ⟨u, hu⟩ := hU hB g hg a
  rw [hu]
  exact algebraMap_unit_ne_zero u

theorem Δ_last (a : Fin G.s) (ha : ¬ (a : ℕ) + 1 < G.s) (g : GL (Fin n) k) :
    G.Δ a g = (g : Matrix (Fin n) (Fin n) k).det := by
  have hall : ∀ i : Fin n, G.bl i ≤ a := by
    intro i
    have := (G.bl i).isLt
    rw [Fin.le_def]
    omega
  unfold Δ
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv hall) _

theorem factor_mul (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) (a : Fin G.s) :
    chk (G.μ a / G.μnext a) (G.Δ a (g * h)) =
      chk (G.μ a / G.μnext a) (G.Δ a g) * chk (G.μ a / G.μnext a) (G.Δ a h) := by
  have hgz := Δ_ne_zero G hU hB hg a
  have hhz := Δ_ne_zero G hU hB hh a
  by_cases ha : (a : ℕ) + 1 < G.s
  · obtain ⟨u, hu1, hu⟩ := hM hC hB g hg h hh a ha
    have hn : G.μnext a = G.μ ⟨a + 1, ha⟩ := by unfold μnext; rw [dite_eq_left ha]
    have hres : ((res (G.μ a / G.μnext a) u : ℂˣ) : ℂ) = 1 := by
      rw [hn, hB.2.2.2 a ⟨a + 1, ha⟩ u hu1, Units.val_one]
    rw [hu, chk_mul _ (mul_ne_zero hgz hhz) (algebraMap_unit_ne_zero u), chk_unit, hres, mul_one,
      chk_mul _ hgz hhz]
  · rw [Δ_last G a ha, Δ_last G a ha, Δ_last G a ha, Units.val_mul, Matrix.det_mul]
    rw [← Δ_last G a ha g, ← Δ_last G a ha h]
    exact chk_mul _ hgz hhz

theorem lam_mul_of (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) : G.lam (g * h) = G.lam g * G.lam h := by
  unfold lam
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => factor_mul G hC hU hM hB hg hh a

end P_lamMul

theorem step_lamMul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : LambdaMultiplicativeProp G := by
  intro hC hU hM hB g hg h hh
  exact P_lamMul.lam_mul_of G hC hU hM hB hg hh

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CS (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (CS ψ) := rfl

theorem CS_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c d : ℕ} (hc : c ∈ CS ψ) (hcd : c ≤ d) : d ∈ CS ψ := by
  intro u hu
  exact hc u (Ideal.pow_le_pow_right hcd hu)

theorem CS_inv (ψ : 𝒪[k]ˣ →* ℂˣ) : CS ψ⁻¹ = CS ψ := by
  ext c
  simp only [CS, Set.mem_setOf_eq, MonoidHom.inv_apply, inv_eq_one]

theorem cond_one : cond (1 : 𝒪[k]ˣ →* ℂˣ) = 0 := by
  rw [cond_eq]
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  rfl

theorem res_div_swap {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) :
    res (μ b / μ a) = (res (μ a / μ b))⁻¹ := by
  ext u
  simp [res, MonoidHom.div_apply, MonoidHom.inv_apply, inv_div]

theorem res_div_mul {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s) (u : 𝒪[k]ˣ) :
    res (μ a / μ c) u = res (μ a / μ b) u * res (μ b / μ c) u := by
  simp [res, MonoidHom.div_apply, div_mul_div_cancel₀]

theorem cc_self {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a : Fin s) : cc μ a a = 0 := by
  unfold cc
  rw [div_self']
  exact cond_one

theorem cc_comm {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : cc μ a b = cc μ b a := by
  unfold cc
  rw [res_div_swap μ a b, cond_eq, cond_eq, CS_inv]

theorem cc_ultra {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s)
    (hab : (CS (res (μ a / μ b))).Nonempty) (hbc : (CS (res (μ b / μ c))).Nonempty) :
    cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  have h1 : cc μ a b ∈ CS (res (μ a / μ b)) := Nat.sInf_mem hab
  have h2 : cc μ b c ∈ CS (res (μ b / μ c)) := Nat.sInf_mem hbc
  have h3 : max (cc μ a b) (cc μ b c) ∈ CS (res (μ a / μ c)) := by
    intro u hu
    rw [res_div_mul μ a b c u,
      CS_mono _ h1 (le_max_left _ _) u hu, CS_mono _ h2 (le_max_right _ _) u hu, one_mul]
  exact Nat.sInf_le h3

theorem step_ccBasic_of_cond :
    ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
      (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c →
        res (μ a / μ b) u = 1) →
      ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  intro s μ hμ a b c
  refine ⟨cc_self μ a, cc_comm μ a b, cc_ultra μ a b c ?_ ?_⟩
  · obtain ⟨c0, h⟩ := hμ a b
    exact ⟨c0, h⟩
  · obtain ⟨c0, h⟩ := hμ b c
    exact ⟨c0, h⟩

end CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_ccBasic : CompactConductorBasicProp (k := k) :=
  CharacterConductor.step_ccBasic_of_cond

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamUnip
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamUnip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_eq_one_of_blockTri {ι β : Type} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (M : Matrix ι ι k) (b : ι → β) (hT : M.BlockTriangular b)
    (hD : ∀ i j, b i = b j → M i j = if i = j then 1 else 0) : M.det = 1 := by
  rw [hT.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have h1 : M.toSquareBlock b c = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    change M i j = (1 : Matrix {a' // b a' = c} {a' // b a' = c} k) ⟨i, hi⟩ ⟨j, hj⟩
    rw [Matrix.one_apply, hD i j (hi.trans hj.symm)]
    simp [Subtype.ext_iff]
  rw [h1, det_one]

theorem delta_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0)
    (a : Fin G.s) : G.Δ a g = 1 := by
  unfold Grp.Δ
  refine det_eq_one_of_blockTri _ (fun i : {i : Fin n // G.bl i ≤ a} => b (G.bl i.1)) ?_ ?_
  · intro i j h
    exact hT i.1 j.1 h
  · intro i j h
    change (g : Matrix (Fin n) (Fin n) k) i.1 j.1 = _
    rw [hD i.1 j.1 h]
    simp [Subtype.ext_iff]

theorem chk_one (μ : kˣ →* ℂˣ) : Grp.chk μ (1 : k) = 1 := by
  unfold Grp.chk
  rw [dite_eq_right one_ne_zero]
  have h : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
  rw [h, map_one, Units.val_one]

theorem lam_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) :
    G.lam g = 1 := by
  unfold Grp.lam
  refine Finset.prod_eq_one fun a _ => ?_
  rw [delta_eq_one G g b hT hD a, chk_one]

theorem diag_of_unipRad {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (hg : g ∈ unipRad k G.e) :
    ∀ i j, G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  have hD := (mem_unipRad.1 hg).2
  intro i j h
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  have hab : a = b := by simpa [Grp.bl] using h
  subst hab
  rw [hD a i' j', Matrix.one_apply]
  by_cases hij : i' = j'
  · subst hij; simp
  · rw [if_neg hij, if_neg]
    intro he
    have := G.e.injective he
    simp at this
    exact hij this

end UpperTheory.TNZ.Grp.P_lamUnip

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamUnip {n : ℕ} (G : Grp k n) : G.LambdaUnipotentProp := by
  refine ⟨fun u hu => ?_, fun u hu _ => ?_⟩
  · obtain ⟨hN, hK⟩ := Subgroup.mem_inf.1 hu
    have hP := (mem_unipRad.1 hN).1
    have hT : ∀ i j, G.bl j < G.bl i → ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 :=
      fun i j h => mem_parab.1 hP i j h
    refine ⟨⟨hK, fun i j hij => ?_⟩, P_lamUnip.lam_eq_one G u (fun a => a) hT
      (P_lamUnip.diag_of_unipRad G u hN)⟩
    rw [hT i j hij]
    exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · exact P_lamUnip.lam_eq_one G u (fun a => OrderDual.toDual a) (fun i j h => (hu i j).1 h)
      (fun i j h => (hu i j).2 h)

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    simp only [map_sub, map_mul, map_pow, map_one] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c * 1 := by gcongr
      _ < γ := by rw [mul_one]; exact hc
  have hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hγ hv
  rw [hV] at hmem
  exact (MonoidHom.mem_ker).mp hmem

theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
end
end

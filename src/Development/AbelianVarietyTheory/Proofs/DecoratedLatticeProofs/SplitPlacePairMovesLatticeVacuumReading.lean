module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatSubTwoNsmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatApprox

theorem two_nsmul_cancel {D : D7} (a b : AE D) (h : (2 : ℕ) • a = (2 : ℕ) • b) : a = b := by
  have key : ∀ c : AE D, c = algebraMap D.host.F (AE D) (2 : D.host.F)⁻¹ * ((2 : ℕ) • c) := by
    intro c
    rw [nsmul_eq_mul, ← mul_assoc, Nat.cast_ofNat, show (2 : AE D) = algebraMap D.host.F (AE D) 2 from (map_ofNat _ 2).symm,
      ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  rw [key a, key b, h]

theorem map_eq_zero_apply {D : D7} {S T : HSp D} {R : Type} [Semiring R] (f : AE D →+* R) {x : WO S T}
    (hx : x.map f = 0) (i : Fin T.rank) (j : Fin S.rank) : f (x i j) = 0 := by
  have := congrFun (congrFun hx i) j
  rwa [Matrix.map_apply, Matrix.zero_apply] at this

theorem eq_two_nsmul {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x l : WO S T} (hx : x.map (infPart D) = 0) (hl : l ∈ latO S T LS LT fun _ => True)
    (hf : (x - (2 : ℕ) • l).map (finPart D) = 0) : x = (2 : ℕ) • l := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ (map_eq_zero_apply _ hf i j)
  rw [Matrix.sub_apply, Matrix.smul_apply, map_sub, map_nsmul, map_eq_zero_apply _ hx i j,
    GlobalTheory.LatVac.infPart_of_mem hl i j, nsmul_zero, sub_zero]

theorem exists_rat_sub_two_nsmul : ∀ (D : D7) (S T : HSp D) (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ γ, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ u - GlobalTheory.LatVac.finTens 1 γ = 2 • l := by
  intro D S T ΛS ΛS' ΛT ΛT' hS hS' hT hT' u hu
  let H : AddSubgroup (WO S T) :=
    ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓
      (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True)).map
      (nsmulAddMonoidHom 2)
  have hH : ∃ U : Set (WO S T), IsOpen U ∧ ∀ x : WO S T, x.map (infPart D) = 0 → (x ∈ H ↔ x ∈ U) := by
    refine ⟨_, (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos).inter
      (GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS' ΛT' hS' hT' 2 two_pos), fun x hx => ⟨?_, ?_⟩⟩
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l, hl.1, ?_⟩, ⟨l, hl.2, ?_⟩⟩ <;>
        rw [nsmulAddMonoidHom_apply, sub_self, Matrix.map_zero _ (map_zero _)]
    · rintro ⟨⟨l, hl, hf⟩, ⟨l', hl', hf'⟩⟩
      have e1 := eq_two_nsmul hx hl hf
      have e2 := eq_two_nsmul hx hl' hf'
      have hll : l = l' := by
        ext i j
        exact two_nsmul_cancel _ _ (by rw [← Matrix.smul_apply, ← Matrix.smul_apply, ← e1, ← e2])
      subst hll
      exact ⟨l, ⟨hl, hl'⟩, by rw [nsmulAddMonoidHom_apply, ← e1]⟩
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.AdTh.SplitClass.exists_rat_sub_mem (LS := (ΛS' : Set (Fin S.rank → D.host.E)))
    (LT := (ΛT' : Set (Fin T.rank → D.host.E))) hH hu
  obtain ⟨l, hl, hle⟩ := hγ
  exact ⟨γ, l, hl.1, hl.2, by rw [← hle, nsmulAddMonoidHom_apply]⟩

end GlobalTheory.LatApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InterEqSumReps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

theorem reps_bijective {V : Type} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) {ι : Type} (s : Finset ι) (z : ι → V)
    (hz : ∀ i ∈ s, z i ∈ A₂) (hinj : ∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j)
    (hsurj : ∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) :
    Function.Bijective (fun i : s => ((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
  constructor
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : z j - z i ∈ A₁ := by simpa [neg_add_eq_sub] using h
    exact Subtype.ext (hinj j hj i hi this).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨i, hi, hyi⟩ := hsurj y hy
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hyi

theorem inter_eq_sum_reps : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ)
    (A₁ A₂ : AddSubgroup V), Formalism.L2.Th1.H.IsHerm H → Formalism.L2.Th1.H.IsSelfDual H A₂ →
    Formalism.L2.Th1.H.IsSemiChar H A₁ α → Formalism.L2.Th1.H.IsSemiChar H A₂ α → ∀ {ι : Type} (s : Finset ι) (z : ι → V),
    (∀ i ∈ s, z i ∈ A₂) → (∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j) → (∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) →
    ∀ F ∈ Formalism.L2.Th1.H.fixedBy H α A₁, ∀ w, Formalism.L2.Th1.H.inter H α A₁ A₂ F w =
      ((Real.sqrt (s.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, α (z i) * Formalism.L2.Th1.H.opU H (z i) F w := by
  intro V _ _ H α A₁ A₂ hH hd₂ hs₁ hs₂ ι s z hz hinj hsurj F hF w
  classical
  have hφ := reps_bijective A₁ A₂ s z hz hinj hsurj
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Finite.of_surjective _ hφ.2
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = s.card := by
    rw [← Fintype.card_of_bijective hφ, Fintype.card_coe]
  have hinv : ∀ (a : A₂), ∀ t ∈ A₁.addSubgroupOf A₂,
      α ((a + t : A₂) : V) * opU H ((a + t : A₂) : V) F w = α (a : V) * opU H (a : V) F w := by
    intro a t ht
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 t.2,
      opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 ht), opU_mul, ← mul_assoc (α t), alpha_sq hs₂ t.2, one_mul]
  rw [congrFun (inter_eq (H := H) (α := α) A₁ A₂ F) w, hcard]
  congr 1
  rw [← Finset.sum_coe_sort s]
  refine (Fintype.sum_bijective _ hφ _ _ fun i => ?_).symm
  have ht : -(⟨z i, hz i i.2⟩ : A₂) + Quotient.out (((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) ∈
      A₁.addSubgroupOf A₂ := by
    rw [← QuotientAddGroup.eq]
    exact (QuotientAddGroup.out_eq' _).symm
  have := hinv ⟨z i, hz i i.2⟩ _ ht
  rw [add_neg_cancel_left] at this
  exact this.symm

end GlobalTheory.ThetaInter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.SplitGen

variable {D : D7}

theorem xiN_smul (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    (c : ℂ) (f : WO S T → ℂ) : xiN θ S T hS hT δ sc (c • f) = c • xiN θ S T hS hT δ sc f := by
  funext z
  simp only [xiN, Pi.smul_apply, smul_eq_mul]
  ring

theorem xiN_sum (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ) :
    xiN θ S T hS hT δ sc (∑ i ∈ s, F i) = ∑ i ∈ s, xiN θ S T hS hT δ sc (F i) := by
  funext z
  simp only [xiN, Finset.sum_apply, Finset.mul_sum]

theorem cartan_of_gram (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have e : gramAt D V τ = 1 := by
    unfold gramAt; rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e]
  exact ⟨by simp, by simp, by
    open scoped ComplexOrder in simpa using Matrix.PosDef.one⟩

theorem toHom_sub (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    toHom S T hS hT (γ - γ') = toHom S T hS hT γ - toHom S T hS hT γ' := by
  unfold toHom
  rw [← map_sub]
  rfl

theorem heisO_add_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {x l : WO S T} {X : WO S T → ℂ}
    (h2 : heisO ψ S T (2 • l) X = X) (hph : ψ (symplO S T x l) = 1) :
    heisO ψ S T (x + 2 • l) X = heisO ψ S T x X := by
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ x (2 • l) X
  rw [h2] at h1
  have h3 : ψ (symplOH S T x (2 • l)) = 1 := by
    rw [two_nsmul]
    have e : symplOH S T x (l + l) = symplOH S T x l + symplOH S T x l := by
      simp only [symplOH, GlobalTheory.LatVac.symplO_add_right, mul_add]
    rw [e, ψ.map_add_eq_mul]
    exact GlobalTheory.LatVac.char_half hph
  rw [h1, h3, one_smul]


set_option maxHeartbeats 1600000 in
theorem moves_reading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove
    A₁ A₂ hA₁ hA₂ hA₂γ hsd hα₁ hα₂ hidx f hf hfix₁ hfix₂ hne
  classical
  have hψ := hW.std
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he

  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T μ μ om hW hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) _ _ _ _ s s' (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs])
    (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs']) hmove f hf
  have hdΛ : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS hΛT hu hu'
  have hdΛ' : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS' hΛT' hu hu'
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hoff : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      (1 - (e + cA D e)) • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [GlobalTheory.SplitScalar.off_smul_actO hs hs', sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  have hfo : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.LatVac.finTens 1 γ) := fun γ => (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl
  have hzsub : ∀ γ γ', embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT γ') =
      embH (tauE D) δ (toHom S T hS hT (γ - γ')) := fun γ γ' => by rw [toHom_sub, map_sub]
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set Λ' := (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ'

  have : (A₁.addSubgroupOf A₂).FiniteIndex := ⟨hidx⟩
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hch : ∀ c : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ γ, ((Quotient.out c : A₂) : VCx D.what₂.Tau a b) =
      embH (tauE D) δ (toHom S T hS hT γ) := fun c => hA₂γ _ (Quotient.out c).2
  choose γc hγc using hch
  have hcov : ∀ u ∈ Λ', ∃ c ∈ (Finset.univ : Finset (A₂ ⧸ A₁.addSubgroupOf A₂)),
      u - GlobalTheory.LatVac.finTens 1 (γc c) ∈ Λ := by
    intro u hu
    obtain ⟨γ, l, hl, hl', hγ⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' u hu
    have hx' : GlobalTheory.LatVac.finTens 1 γ ∈ Λ' := by
      rw [show GlobalTheory.LatVac.finTens 1 γ = u - 2 • l by rw [← hγ, sub_sub_cancel]]
      exact sub_mem hu (nsmul_mem hl' 2)
    have hz : embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂ := (hA₂ γ _ (hfo γ)).1 hx'
    refine ⟨QuotientAddGroup.mk (⟨_, hz⟩ : A₂), Finset.mem_univ _, ?_⟩
    have hq : embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) ∈ A₁ := by
      rw [← hγc]
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (A₁.addSubgroupOf A₂) (⟨_, hz⟩ : A₂)
      rw [hh, AddSubgroup.coe_add, sub_add_cancel_left]
      exact neg_mem (AddSubgroup.mem_addSubgroupOf.1 h.2)
    rw [hzsub] at hq
    have h1 := (hA₁ _ _ (hfo _)).2 hq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    have e1 : u - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂))) =
        2 • l + (GlobalTheory.LatVac.finTens 1 γ - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) := by
      rw [← hγ]; abel
    rw [e1]
    exact add_mem (nsmul_mem hl 2) h1
  obtain ⟨R, hR, hRu⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf e u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  obtain ⟨R', hR', hRu'⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf (cA D e) u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  have hRu2 : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ := fun u hu hue => hRu u ⟨hu, hue⟩
  have hRu2' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ := fun u hu hue => hRu' u ⟨hu, hue⟩
  have hmain := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T μ μ om hW hP.inf hP.sigS hP.sigT
    (fun _ => 1) (fun _ => 1) (cartan_of_gram S hP.gS) (cartan_of_gram T hP.gT) ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT'
    e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove R R' hR hRu2 hR' hRu2' f hf

  have hpair : ∀ p : WO S T × WO S T, ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ l : WO S T,
      p ∈ R ×ˢ R' → (l ∈ Λ ∧ l ∈ Λ' ∧ p.1 + p.2 - GlobalTheory.LatVac.finTens 1 γ = 2 • l) := by
    intro p
    by_cases hp : p ∈ R ×ˢ R'
    · obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
      obtain ⟨γ, l, h1, h2, h3⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' (p.1 + p.2)
        (add_mem (hR _ hu).1 (hR' _ hu').1)
      exact ⟨γ, l, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose γ l hγl using hpair
  have hxeq : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) = p.1 + p.2 - 2 • l p := fun p hp => by
    rw [← (hγl p hp).2.2, sub_sub_cancel]
  have hxΛ' : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) ∈ Λ' := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    rw [hxeq p hp]
    exact sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (nsmul_mem (hγl p hp).2.1 2)
  have hwx : ∀ p ∈ R ×ˢ R', p.1 + p.2 = GlobalTheory.LatVac.finTens 1 (γ p) + 2 • l p := fun p hp => by
    rw [hxeq p hp, sub_add_cancel]
  have hz₂ : ∀ p ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₂ := fun p hp =>
    (hA₂ _ _ (hfo _)).1 (hxΛ' p hp)

  have hpf : ∀ p ∈ R ×ˢ R', heisO ψ S T p.1 (heisO ψ S T p.2 f) =
      ψ (symplOH S T p.1 p.2) • heisO ψ S T (GlobalTheory.LatVac.finTens 1 (γ p)) f := by
    intro p hp
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hf.2.lat.1 _ (hγl p hp).1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)]

  have hph : ∀ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) = alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    have hF : heisO ψ S T p.1 (heisO ψ S T p.2 (om (s, s') f)) = om (s, s') f := by
      rw [hom.2.lat.2 _ he' p.2 (hR' _ hu').1 (hR' _ hu').2, hom.2.lat.2 _ he p.1 (hR _ hu).1 (hR _ hu).2]
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hom.2.lat.1 _ (hγl p hp).2.1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)] at hF
    have hG := congrArg (xiN θ S T hS hT δ sc) hF
    rw [xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hom.2.theta _ _ (hfo _)] at hG
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hG w
    have h2 := hfix₂ _ (hz₂ p hp) w
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
    have hU : Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc (om (s, s') f)) w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact hw h1.symm
    exact mul_right_cancel₀ hU (h1.trans h2.symm)

  have hinj : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) -
      embH (tauE D) δ (toHom S T hS hT (γ q)) ∈ A₁ → p = q := by
    intro p hp q hq hpq
    rw [hzsub] at hpq
    have h1 := (hA₁ _ _ (hfo _)).2 hpq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    by_contra hne'
    refine GlobalTheory.SplitScalar.sum_sub_notMem he hst hstc hR hRu2 hR' hRu2' hu hv hu' hv'
      (by rw [Prod.mk.eta, Prod.mk.eta]; exact hne') ?_
    have e2 : p.1 + p.2 - (q.1 + q.2) = (GlobalTheory.LatVac.finTens 1 (γ p) - GlobalTheory.LatVac.finTens 1 (γ q)) +
        2 • (l p - l q) := by
      rw [hwx p hp, hwx q hq]; abel
    rw [e2]
    exact add_mem h1 (nsmul_mem (sub_mem (hγl p hp).1 (hγl q hq).1) 2)
  have hsurj : ∀ y ∈ A₂, ∃ p ∈ R ×ˢ R', y - embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₁ := by
    intro y hy
    obtain ⟨γ₀, rfl⟩ := hA₂γ y hy
    have hv : GlobalTheory.LatVac.finTens 1 γ₀ ∈ Λ' := (hA₂ _ _ (hfo _)).2 hy
    have hh1 : IsHalf e (e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he.1])
    have hh2 : IsHalf (cA D e) (cA D e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he'.1])
    obtain ⟨r, ⟨hr, hrΛ⟩, -⟩ := hRu2 _ (hst' _ hv) hh1
    obtain ⟨r', ⟨hr', hrΛ'⟩, -⟩ := hRu2' _ (hstc' _ hv) hh2
    have hp : (r, r') ∈ R ×ˢ R' := Finset.mem_product.2 ⟨hr, hr'⟩
    refine ⟨(r, r'), hp, ?_⟩
    rw [hzsub]
    refine (hA₁ _ _ (hfo _)).1 ?_
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub, hxeq _ hp]
    have e3 : GlobalTheory.LatVac.finTens 1 γ₀ - ((r, r').1 + (r, r').2 - 2 • l (r, r')) =
        (e • GlobalTheory.LatVac.finTens 1 γ₀ - r) + (cA D e • GlobalTheory.LatVac.finTens 1 γ₀ - r') +
        (1 - (e + cA D e)) • GlobalTheory.LatVac.finTens 1 γ₀ + 2 • l (r, r') := by
      simp only [sub_smul, add_smul, one_smul]; abel
    rw [e3]
    exact add_mem (add_mem (add_mem hrΛ hrΛ') (hoff _ hv)) (nsmul_mem (hγl _ hp).1 2)
  have hsum := GlobalTheory.ThetaInter.inter_eq_sum_reps (HV sc) (alV D.host.d sc) A₁ A₂ (herm_HV sc) hsd hα₁ hα₂ (R ×ˢ R')
    (fun p => embH (tauE D) δ (toHom S T hS hT (γ p))) hz₂ hinj hsurj _ hfix₁

  have hF : xiN θ S T hS hT δ sc (om (s, s') f) =
      ((splitFacO μ μ x₀ y₀ : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) •
      ∑ p ∈ R ×ˢ R', alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) •
        Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc f) := by
    rw [hmain, xiN_smul, ← Finset.sum_product', xiN_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hpf p hp, xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hf.2.theta _ _ (hfo _),
      hph p hp]
  funext w
  rw [hF, hsum w]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, splitFacO, Circle.coe_mul, Circle.coe_inv,
    Finset.card_product, Nat.cast_mul]
  ring

end GlobalTheory.AdForm.SplitGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReadingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  first | exact @GlobalTheory.AdForm.SplitGen.moves_reading | exact GlobalTheory.AdForm.SplitGen.moves_reading | (intros; apply GlobalTheory.AdForm.SplitGen.moves_reading <;> assumption)
end

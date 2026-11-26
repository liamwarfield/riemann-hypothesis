module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem conj_level {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  have e : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) =
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)) ⁻¹' (U : Set G) := by
    ext u
    simp
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · rw [e]; exact h1.preimage (Homeomorph.continuous _)
  · rw [e]; exact (Homeomorph.isCompact_preimage _).2 h2

theorem UpperTheory.V.Cj.exactSub :
    UpperTheory.V.Cj.ExactSub := by
  intro E _ _ _ a Ξ q
  have comb : ∀ (s : ℂ) (α β : Co Ξ q), Exact Ξ α → Exact Ξ β → Exact Ξ (s • α + β) := by
    rintro s α β ⟨U, u1, u2, hα⟩ ⟨V, v1, v2, hβ⟩
    have hα' := ((levSub E a Ξ q).2.1 U (U ⊓ V) inf_le_left α).2 hα
    have hβ' := ((levSub E a Ξ q).2.1 V (U ⊓ V) inf_le_right β).2 hβ
    refine ⟨U ⊓ V, u1.inter v1, u2.inter_right (V.isClosed_of_isOpen v1), ?_⟩
    cases q with
    | zero =>
      change α = 0 at hα'
      change β = 0 at hβ'
      change s • α + β = 0
      rw [hα', hβ', smul_zero, add_zero]
    | succ q =>
      obtain ⟨η, e1, rfl⟩ := hα'
      obtain ⟨ζ, z1, rfl⟩ := hβ'
      exact ⟨s • η + ζ, (levSub E a Ξ q).1 _ s η ζ e1 z1, dCo_comb s η ζ⟩
  have hz : Exact Ξ (0 : Co Ξ q) := by
    obtain ⟨L, hL, -⟩ := (levSub E a Ξ q).2.2
    obtain ⟨U, u1, u2, -⟩ := (hL 0).1 L.zero_mem
    refine ⟨U, u1, u2, ?_⟩
    cases q with
    | zero => rfl
    | succ q =>
      exact ⟨0, ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩,
        AlternatingMap.ext fun X => by simp [dCo_apply]⟩
  refine ⟨{ carrier := {ω | Exact Ξ ω}
            add_mem' := fun {α β} hα hβ => by simpa only [one_smul, Set.mem_ofPred_eq] using comb 1 α β hα hβ
            zero_mem' := hz
            smul_mem' := fun s α hα => by simpa only [add_zero, Set.mem_ofPred_eq] using comb s α 0 hα hz }, fun _ => Iff.rfl, ?_⟩
  rintro x ω ⟨U, u1, u2, hω⟩
  obtain ⟨U', v1, v2, hx⟩ := conj_level U u1 u2 x
  refine ⟨U', v1, v2, ?_⟩
  cases q with
  | zero =>
    change ω = 0 at hω
    change trans x ω = 0
    rw [hω, ← transRep_apply, map_zero]
  | succ q =>
    obtain ⟨η, e1, rfl⟩ := hω
    obtain ⟨p1, p2, -⟩ := perNat E a U U' x hx Ξ q η e1
    exact ⟨trans x η, p1, p2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.HarmSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rT_adj (r : ℝ) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smAdj Ξ r X m) = smAdj Ξ r X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h : lie E a X * act (.fin x) = act (.fin x) * lie E a X := lie_rt_fin X x
  have h1 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smA Ξ X m) = smA Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smA_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, h]
  have h2 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smB Ξ X m) = smB Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smB_apply]
    clear h1
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
    | tmul φ v => simp
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, LinearMap.map_smul_of_tower]

variable {π : CuspSub E a} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem cocl_comb {q : ℕ} (s : ℂ) {ω η : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω)
    (hη : Coclosed (smAdj Ξ r) e η) : Coclosed (smAdj Ξ r) e (s • ω + η) := by
  have ap : ∀ X, (s • ω + η) X = s • ω X + η X := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

private theorem cocl_zero {q : ℕ} : Coclosed (smAdj Ξ r) e (0 : Geo.Co Ξ q) := by
  cases q with
  | zero => trivial
  | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem cocl_trans {q : ℕ} (x : GL (Fin a) (Af E)) {ω : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω) :
    Coclosed (smAdj Ξ r) e (Geo.trans x ω) := by
  have ap : ∀ X, Geo.trans x ω X = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (ω X) := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ap, ← rT_adj, ← map_sum, h1, map_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.harmSub :
    UpperTheory.V.Cj.HarmSub := by
  intro E _ _ _ a π Ξ r n e q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsPiHarm π Ξ r e α → IsPiHarm π Ξ r e β → IsPiHarm π Ξ r e (s • α + β) :=
    fun s α β hα hβ => ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.1)) ((L1 _).2 hβ.1)),
      by rw [dCo_comb, hα.2.1, hβ.2.1, smul_zero, add_zero], cocl_comb s hα.2.2.1 hβ.2.2.1,
      fun X => Submodule.add_mem _ (Submodule.smul_mem _ s (hα.2.2.2 X)) (hβ.2.2.2 X)⟩
  have zero : IsPiHarm π Ξ r e (0 : Geo.Co Ξ q) :=
    ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], cocl_zero, fun X => Submodule.zero_mem _⟩
  refine ⟨{ carrier := {ω | IsPiHarm π Ξ r e ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ },
    fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, cocl_trans x h3, fun X => mem_tens.2 fun i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact π.stable (.fin x) _ (mem_tens.1 (h4 X) i)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelFacts
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.CobLin
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem geo_hd_smul_add {Γ M : Type} [AddCommGroup M] [Module ℂ M] (s : ℂ)
    (b b' : List Γ → M) (x : List Γ) :
    UpperTheory.V.Lit.Geo.hd (s • b + b') x =
      s • UpperTheory.V.Lit.Geo.hd b x + UpperTheory.V.Lit.Geo.hd b' x := by
  unfold UpperTheory.V.Lit.Geo.hd
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, Pi.smul_apply, smul_add, smul_comm]

theorem UpperTheory.V.Cj.cobLin :
    UpperTheory.V.Cj.CobLin := by
  intro Γ M _ _ _ ρ q s c c' hc hc'
  cases q with
  | zero =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    intro x hx
    rw [Pi.add_apply, Pi.smul_apply, hc x hx, hc' x hx, smul_zero, add_zero]
  | succ k =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    obtain ⟨b, hbe, hbc⟩ := hc
    obtain ⟨b', hbe', hbc'⟩ := hc'
    refine ⟨s • b + b', fun γ x hx => ?_, fun x hx => ?_⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hbe γ x hx, hbe' γ x hx,
        map_add, map_smul]
    · rw [geo_hd_smul_add, Pi.add_apply, Pi.smul_apply, hbc x hx, hbc' x hx]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelLin
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relLin :
    UpperTheory.V.Cj.RelLin := by
  intro E _ _ _ a U σ Ξ Ξ' h q s α α' β β' ⟨a1, b1, c, d, p1, p2, p3⟩ ⟨a2, b2, c', d', r1, r2, r3⟩
  refine ⟨(levSub E a Ξ q).1 U s _ _ a1 a2, (levSub E a Ξ' q).1 U (σ s) _ _ b1 b2, s • c + c', σ s • d + d', ?_, ?_, ?_⟩
  · simpa only [one_smul] using (perEx E a U Ξ q).2.2 α α' c c' s 1 p1 r1
  · simpa only [one_smul] using (perEx E a U Ξ' q).2.2 β β' d d' (σ s) 1 p2 r2
  · have e : σ s • d + d' - sigC σ h (s • c + c') = σ s • (d - sigC σ h c) + (d' - sigC σ h c') := by
      funext z y i
      simp only [sigC, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
      ring
    rw [e]
    exact cobLin _ _ _ q (σ s) _ _ p3 r3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelKer
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.SigCob
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem hcob_map {Γ M M' : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ M') (T : M →+ M') (hT : ∀ γ m, T (ρ γ m) = ρ' γ (T m))
    (q : ℕ) (c : List Γ → M) (hc : HCob ρ q c) : HCob ρ' q (fun x => T (c x)) := by
  cases q with
  | zero =>
    intro x hx
    change T (c x) = 0
    rw [hc x hx, map_zero]
  | succ k =>
    obtain ⟨b, b1, b2⟩ := hc
    refine ⟨fun x => T (b x), fun γ x hx => ?_, fun x hx => ?_⟩
    · change T (b _) = _
      rw [b1 γ x hx, hT]
    · change T (c x) = _
      rw [b2 x hx]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hd, map_sum, map_zsmul]

private theorem sigCob_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) (hσ : ConjMat σ h) (q : ℕ)
    (c : List ↥(⊤ : Subgroup (GL (Fin a) E)) → (GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ)
    (hc : HCob (levelRep ⊤ U (ratC Ξ)) q c) : HCob (levelRep ⊤ U (ratC Ξ')) q (sigC σ h c) := by
  let T : ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ) →+ ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ'.d → ℂ) :=
    { toFun := fun f y i => σ (f y (Fin.cast h.symm i))
      map_zero' := by ext y i; simp
      map_add' := fun f g => by ext y i; simp }
  refine hcob_map _ _ T (fun γ f => ?_) q c hc
  funext y i
  change σ ((ratC Ξ γ *ᵥ f _) (Fin.cast h.symm i)) = (ratC Ξ' γ *ᵥ fun j => σ (f _ (Fin.cast h.symm j))) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hσ _ _ _]
  exact Fintype.sum_equiv (finCongr h) _ _ fun j => rfl

theorem UpperTheory.V.Cj.sigCob :
    UpperTheory.V.Cj.SigCob := by
  intro E _ _ _ a U σ Ξ Ξ' h hσ q c
  refine ⟨fun hc => ?_, sigCob_one U σ h hσ q c⟩
  have hσ' : ConjMat σ.symm h.symm := fun γ i j => by
    rw [RingEquiv.eq_symm_apply, ← hσ]; rfl
  have e : sigC σ.symm h.symm (sigC σ h c) = c := by
    funext z y i
    exact σ.symm_apply_apply _
  have := sigCob_one U σ.symm h.symm hσ' q _ hc
  rwa [e] at this
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem cob_sub {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c - c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q (-1) c' c h' h
  rwa [neg_smul, one_smul, neg_add_eq_sub] at this

private theorem cob_add {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c + c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q 1 c c' h h'
  rwa [one_smul] at this

theorem UpperTheory.V.Cj.relKer :
    UpperTheory.V.Cj.RelKer := by
  intro E _ _ _ a ha U hU σ Ξ Ξ' h hσ q α β
  have hs := UpperTheory.V.Cj.sigCob E a U σ Ξ Ξ' h hσ q
  refine ⟨?_, fun a1 b1 a2 b2 a3 b3 => ?_⟩
  · rintro ⟨a1, b1, c, c', p, p', hc⟩
    rw [← perKer E a ha U hU Ξ q α c a1 p, ← perKer E a ha U hU Ξ' q β c' b1 p', ← hs c]
    constructor
    · intro k
      have := cob_add hc k
      rwa [sub_add_cancel] at this
    · intro k
      have := cob_sub k hc
      rwa [sub_sub_cancel] at this
  · obtain ⟨c, p⟩ := (perEx E a U Ξ q).1 α a1 a2
    obtain ⟨c', p'⟩ := (perEx E a U Ξ' q).1 β b1 b2
    exact ⟨a1, b1, c, c', p, p', cob_sub ((perKer E a ha U hU Ξ' q β c' b1 p').2 b3)
      ((hs c).2 ((perKer E a ha U hU Ξ q α c a1 p).2 a3))⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelPull
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem cob_map {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ N) (P : M →ₗ[ℂ] N) (hP : ∀ γ m, P (ρ γ m) = ρ' γ (P m))
    (q : ℕ) (c : List Γ → M) (h : HCob ρ q c) : HCob ρ' q (fun z => P (c z)) := by
  cases q with
  | zero =>
    intro z hz
    beta_reduce
    rw [h z hz, map_zero]
  | succ q =>
    obtain ⟨b, b1, b2⟩ := h
    refine ⟨fun z => P (b z), fun γ z hz => ?_, fun z hz => ?_⟩
    · beta_reduce
      rw [b1 γ z hz, hP]
    · beta_reduce
      rw [b2 z hz]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hd, map_sum, map_zsmul]

private theorem coset_map {G : Type} [Group G] {U U' : Subgroup G} {x : G} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U) :
    ∃ f : G ⧸ U' → G ⧸ U, (∀ y : G, f y = ((y * x : G) : G ⧸ U)) ∧ ∀ (g : G) s, f (g • s) = g • f s := by
  have wd : ∀ y y' : G, (QuotientGroup.leftRel U') y y' → ((y * x : G) : G ⧸ U) = ((y' * x : G) : G ⧸ U) := by
    intro y y' hy
    have h1 := hx _ (QuotientGroup.leftRel_apply.1 hy)
    refine QuotientGroup.eq.2 ?_
    convert h1 using 1
    group
  refine ⟨Quotient.lift _ wd, fun _ => rfl, fun g s => ?_⟩
  induction s using QuotientGroup.induction_on with | H y => ?_
  change ((g * y * x : G) : G ⧸ U) = ((g * (y * x) : G) : G ⧸ U)
  rw [mul_assoc]

theorem UpperTheory.V.Cj.relPull :
    UpperTheory.V.Cj.RelPull := by
  intro E _ _ _ a U U' x hx σ Ξ Ξ' h q α β ⟨hα, hβ, c, c', p, p', hc⟩
  obtain ⟨f, f1, f2⟩ := coset_map hx
  obtain ⟨a1, -, a2⟩ := perNat E a U U' x hx Ξ q α hα
  obtain ⟨b1, -, b2⟩ := perNat E a U U' x hx Ξ' q β hβ
  refine ⟨a1, b1, fun z s => c z (f s), fun z s => c' z (f s), a2 c _ (fun z y => by rw [f1]) p,
    b2 c' _ (fun z y => by rw [f1]) p', ?_⟩
  refine cob_map (levelRep ⊤ U (ratC Ξ')) (levelRep ⊤ U' (ratC Ξ')) (LinearMap.funLeft ℂ _ f) (fun γ m => ?_) q _ hc
  funext s
  change _ *ᵥ m (_ • f s) = _ *ᵥ m (f (_ • s))
  rw [f2]
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem oc_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U U' : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (h3 : IsOpen (U' : Set G)) :
    IsOpen ((U ⊓ U' : Subgroup G) : Set G) ∧ IsCompact ((U ⊓ U' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact ⟨h1.inter h3, h2.inter_right (U'.isClosed_of_isOpen h3)⟩

private theorem oc_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x⁻¹ * u * x) ⁻¹' U := by
      ext u; simp
    rw [this]
    exact h1.preimage (by fun_prop)
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x * u * x⁻¹) '' U := by
      ext u
      constructor
      · intro hu
        exact ⟨x⁻¹ * u * x, by simpa using hu, by group⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [mul_assoc] using hv
    rw [this]
    exact h2.image (by fun_prop)

theorem UpperTheory.V.Cj.relFacts :
    UpperTheory.V.Cj.RelFacts := by
  intro E _ _ _ a ha σ Ξ Ξ' h hσ q
  have mono : ∀ U U' : Subgroup (GL (Fin a) (Af E)), U' ≤ U → ∀ (α : Co Ξ q) (β : Co Ξ' q),
      RelAt U σ h α β → RelAt U' σ h α β := fun U U' hU α β hr => by
    have := relPull E a U U' 1 (fun u hu => by simpa using hU hu) σ Ξ Ξ' h q α β hr
    rwa [trans_one, trans_one] at this
  have L := (levSub E a Ξ q).2.1
  have L' := (levSub E a Ξ' q).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s α α' β β' ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    exact ⟨U ⊓ V, w1, w2, relLin E a _ σ Ξ Ξ' h q s α α' β β' (mono _ _ inf_le_left _ _ u3) (mono _ _ inf_le_right _ _ v3)⟩
  · rintro x α β ⟨U, u1, u2, u3⟩
    obtain ⟨V, v1, v2, v3⟩ := oc_conj u1 u2 x
    exact ⟨V, v1, v2, relPull E a U V x v3 σ Ξ Ξ' h q α β u3⟩
  · rintro α β ⟨U, u1, u2, u3⟩
    constructor
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).1
        ((L _ _ inf_le_right α).2 v3)⟩
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).2
        ((L' _ _ inf_le_right β).2 v3)⟩
  · rintro α β ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩ d1 d2 ⟨X, x1, -, x3⟩ ⟨Y, y1, -, y3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    obtain ⟨w3, w4⟩ := oc_inf w1 w2 x1
    obtain ⟨w5, w6⟩ := oc_inf w3 w4 y1
    exact ⟨_, w5, w6, (relKer E a ha _ w6 σ Ξ Ξ' h hσ q α β).2
      ((L _ _ (inf_le_left.trans (inf_le_left.trans inf_le_left)) α).1 u3)
      ((L' _ _ (inf_le_left.trans (inf_le_left.trans inf_le_right)) β).1 v3) d1 d2
      ((L _ _ (inf_le_left.trans inf_le_right) α).2 x3) ((L' _ _ inf_le_right β).2 y3)⟩
end

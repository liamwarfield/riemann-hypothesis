module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityOfArtinCongruence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep

theorem UpperTheory.V.Af.satLoc :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.SatLoc := by
  intro _ F _ _ n w σ
  have hex : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := n)) → ∃ B, HasSatGL w σ.ρ B :=
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
  refine ⟨fun ⟨v, h0, hv⟩ => hex ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩), ?_⟩
  intro V _ _ ρ ⟨hV, htop⟩ B
  have up : ∀ B, HasSatGL w σ.ρ B → HasSatGL w (ρ.comp (locGL F n w)) B := by
    intro B h
    constructor
    · obtain ⟨f, h0⟩ : ∃ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, f.1 ≠ 0 := by
        by_contra hc
        push Not at hc
        refine top_ne_bot (htop.symm.trans (eq_bot_iff.2 (iSup_le fun f => ?_)))
        rw [hc f, LinearMap.range_zero]
      obtain ⟨x, hx⟩ := h.exists_vec
      have hi : LinearMap.ker f.1 = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [f.2, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
      have h1 := hx.map (ρ' := ρ.comp (locGL F n w)) f.1 f.2
        ((map_ne_zero_iff f.1 (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · intro x hx h0
      exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := ρ.comp (locGL F n w)) σ.irred h
        (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
        (htop ▸ Submodule.mem_top) hx h0
  refine ⟨fun h => ?_, up B⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup (ρ.comp (locGL F n w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
    (KGL w (n := n) : Set _) x hx0 (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
  obtain ⟨B', hB'⟩ := hex ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (up B' hB').unique h ▸ hB'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

section

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩

private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩

end

theorem UpperTheory.V.Af.locCompC :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.LocCompC := by
  intro P E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp P.litN.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.Af.isoOfFrob :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IsoOfFrob := by
  intro _ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)

namespace UpperTheory.V.Af.RealLocalComponent

section Gen

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]

private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]

private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this

private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem smooth_fin (π : TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff

private theorem smooth_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
  (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

private theorem fin_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]

private theorem bot_or_top (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

private theorem isotypic (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))

private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)

private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
    fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin n) (pLoc F w)).ker)
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
      rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
        (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
    U (fun g x hx => ⟨fun c hc => by
        rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
      mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
    ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π (L ⊓ (K' ⊓ L.comap (locGL F n w)).comap (GeneralLinearGroup.map (pLoc F w)))
        (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
          (continuous_map_pLoc w))) d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
      refine hWf f hf (fun k hk v => ?_) hx1
      have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
      have h2 := mem_fix.1 hx.2 _ hk.2.1
      have h3 : π.finPart k x = x := by
        rw [← mul_inv_cancel_left (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
          Module.End.mul_apply, h1]
        exact h2
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), h3])
  exact ⟨σ, hσ⟩

end UpperTheory.V.Af.RealLocalComponent

theorem UpperTheory.V.Af.locCompR :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.LocCompR := fun P _ _ _ _ _ π w =>
  ⟨UpperTheory.V.Af.RealLocalComponent.exists_comp P.admR π w, UpperTheory.V.Af.RealLocalComponent.isotypic π w⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rec_algNorm_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [rec_algNorm H, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end UpperTheory.V.Af

open UpperTheory.V.Af in
theorem UpperTheory.V.Af.satFrob :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.SatFrob := by
  intro P F Ω _ _ _ _ _ l _ ι n r _ w hl σ B hB H A h
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  have hrec : IsRec h rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag hrec σ B hB
  have hx := H A h rc hrec
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleConstituentOfLevelWeilDeligneEqCharac
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_charpoly_dvd {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V)
    (hf : f.IsSemisimple) (hd : f.charpoly ∣ (1 : Module.End ℂ V').charpoly) : f = 1 := by
  rw [LinearMap.charpoly_one] at hd
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)

theorem UpperTheory.irreducible_constituent_of_level_weilDeligne_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ), 1 ≤ M →
    ∀ x z : WD h, UpperTheory.V.Af.IsLevelWD M n x → IsIrrWD z → (∀ σ, z.charPol σ ∣ x.charPol σ) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  intro F Ω _ _ _ _ _ w A h M n hM x z hx hz hd
  obtain ⟨χ, a, hχ, rfl, -, ha⟩ := hx
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h1 : a.ρ (ineIncl h s) = 1 := by
      rw [ha s]
      have : (fun i => ((χ i s : ℂˣ) : ℂ)) = fun _ => 1 := by
        funext i
        rw [hχ i s hs]
        rfl
      rw [this, Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    have h2 := hd (ineIncl h s)
    rw [WD.charPol_mk, WD.charPol_mk, h1] at h2
    exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Af.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2

theorem UpperTheory.V.Af.locFixed :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.LocFixed := by
  intro P F Ω _ _ _ _ _ n M hM w A h rc hrc σ hL
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  by_cases hw : (M : 𝓞 F) ∈ w.asIdeal
  · have hv : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := UpperTheory.V.Af.val_lt_one w hw
    have hM0 : (M : w.adicCompletion F) ≠ 0 := by
      rw [← map_natCast (algebraMap F (w.adicCompletion F)), map_ne_zero]
      exact Nat.cast_ne_zero.2 (by omega)
    have hu0 : uniformizer (w.adicCompletion F) ≠ 0 := by simp
    have hv0 : valuation (w.adicCompletion F) (M : w.adicCompletion F) ≠ 0 := by simpa using hM0
    let γ : (ValueGroupWithZero (w.adicCompletion F))ˣ :=
      Units.mk0 (valuation _ (M : w.adicCompletion F) / uniformizer (w.adicCompletion F)) (div_ne_zero hv0 hu0)
    have hlt : ∀ x : ValueGroupWithZero (w.adicCompletion F),
        x < γ ↔ x ≤ valuation _ (M : w.adicCompletion F) := fun x => by
      show x < _ / _ ↔ _
      rw [lt_div_iff₀ (zero_lt_iff.2 hu0)]
      refine ⟨fun h1 => not_lt.1 fun h2 => h1.not_ge ?_, fun h1 => (mul_le_mul_left h1 _).trans_lt
        (mul_lt_of_lt_one_right (zero_lt_iff.2 hv0) uniformizer_lt_one)⟩
      have hx : 0 < x := (zero_lt_iff.2 hv0).trans h2
      rwa [← div_le_iff₀' hx, le_uniformizer_iff, div_lt_one₀ hx]
    have hγ : γ ≤ 1 := by
      show _ / _ ≤ (1 : ValueGroupWithZero (w.adicCompletion F))
      rw [div_le_one₀ (zero_lt_iff.2 hu0), le_uniformizer_iff]
      exact hv
    obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport P.litN.loc.zel (algNorm σ)
    have hch : ∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : (w.adicCompletion F)ˣ,
        valuation (w.adicCompletion F) ((u : w.adicCompletion F) - 1) < γ → χ u = 1 := fun y hy => by
      obtain ⟨ξ, hξ, e, hξ1⟩ := UpperTheory.irreducible_constituent_of_level_weilDeligne_eq_character F Ω w A h M n hM _ (rc y) hL ((H.cusp y).1 (hs.isCusp hy)) fun τ => by
        rw [H.supp _ s hs τ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol τ) hy)
      obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
      refine ⟨χ, hχ, H.bij.1 (e.trans (H.one χ hχ).symm), fun u hu => ?_⟩
      obtain ⟨τ, rfl⟩ := ha.surj u
      have h1 : valuation (w.adicCompletion F) (a τ : w.adicCompletion F) = 1 := by
        have := (valuation (w.adicCompletion F)).map_one_add_of_lt (hu.trans_le (Units.val_le_val.2 hγ))
        simpa using this
      obtain ⟨h2, h3⟩ := UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence P.litN.aut.art F Ω w A h a ha M hM τ h1 ((hlt _).1 hu)
      exact hξ1 ⟨τ, h2⟩ h3
    have hne := UpperTheory.jacquet_borel_nontrivial_of_character_support P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s hs fun y hy => by
      obtain ⟨χ, hχ, rfl, -⟩ := hch y hy
      rfl
    obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_borel_exists_torus_congruence_fixed P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s γ hγ hs hch hne
    have hf := UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed _ _ _ (algNorm σ).rep γ hγ
      ((P.litN.loc.bz _).1 _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr) y hy0 hy
    refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hf
    exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, fun i j => (hlt _).2 ((UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).2 i j)⟩, hv0⟩
  · obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
    have hu : (rc (algNorm σ)).unr := by
      rw [← e, WD.unr_mk]
      refine ⟨hN, fun s => ?_⟩
      rw [hb s]
      simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char F Ω w A h M hw s s.2), Module.End.one_eq_id]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 ((H.sph _).2 hu)
    refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
    exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).1⟩, hv0⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubgroupFixed
noncomputable def UpperTheory.Reformulated.B.SubgroupFixed.HasFixed :
    {Γ V : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ Γ V → Subgroup Γ → Prop :=
    fun {Γ V : Type} [Group Γ] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) ↦
      ∃ (v : V), v ≠ (0 : V) ∧ ∀ u ∈ U, ((ρ : Γ → V →ₗ[ℂ] V) u : V → V) v = v

private lemma UpperTheory.Reformulated.B.SubgroupFixed.core {R M N : Type*} [Ring R] [AddCommGroup M] [_root_.Module R M]
    [AddCommGroup N] [_root_.Module R N] [IsSimpleModule R M]
    (hsup : ∀ S : Submodule R N, (∀ f : M →ₗ[R] N, LinearMap.range f ≤ S) → S = ⊤)
    (W : Submodule R N) (hW : W ≠ ⊥) :
    ∃ g : M →ₗ[R] N, Function.Injective g ∧ LinearMap.range g ≤ W := by
  have hss : IsSemisimpleModule R N := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun f : M →ₗ[R] N => LinearMap.range f) (fun f => IsSemisimpleModule.range f) ?_
    exact hsup _ (fun f => le_iSup (fun f : M →ₗ[R] N => LinearMap.range f) f)
  obtain ⟨C, hC⟩ := exists_isCompl W
  let p : N →ₗ[R] W := W.linearProjOfIsCompl C hC
  have hex : ∃ f : M →ₗ[R] N, p ∘ₗ f ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : LinearMap.ker p = ⊤ := hsup _ (fun f => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (hno f) x)
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : p w = 0 := by
      have : w ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
      exact this
    have h2 : p w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    have h3 : (⟨w, hw⟩ : W) = 0 := h2.symm.trans h1
    simpa using congrArg Subtype.val h3
  obtain ⟨f, hf⟩ := hex
  have hinj := (LinearMap.injective_or_eq_zero (p ∘ₗ f)).resolve_right hf
  refine ⟨W.subtype ∘ₗ p ∘ₗ f, W.injective_subtype.comp hinj, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (p (f x)).2

theorem UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed :
    ∀ {Γ X V : Type} [inst : Group Γ] [inst_1 : AddCommGroup X] [inst_2 : _root_.Module ℂ X] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (σ : Representation ℂ Γ X),
      σ.IsIrreducible →
        ∀ (τ : Representation ℂ Γ V),
          ⨆ (f :
                { f : X →ₗ[ℂ] V //
                  ∀ (g : Γ) (v : X),
                    (f : X → V) (((σ : Γ → X →ₗ[ℂ] X) g : X → X) v) = ((τ : Γ → V →ₗ[ℂ] V) g : V → V) ((f : X → V) v) }),
                (↑f : X →ₗ[ℂ] V).range =
              ⊤ →
            ∀ (W : Submodule ℂ V),
              (∀ (g : Γ), ∀ v ∈ W, ((τ : Γ → V →ₗ[ℂ] V) g : V → V) v ∈ W) →
                W ≠ ⊥ →
                  ∀ (K : Subgroup Γ),
                    UpperTheory.Reformulated.B.SubgroupFixed.HasFixed σ K → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ u ∈ K, ((τ : Γ → V →ₗ[ℂ] V) u : V → V) v = v := by
  intro Γ X V _ _ _ _ _ σ hσ τ h W hWinv hW K hK
  obtain ⟨x0, hx0, hfix⟩ := hK
  haveI : IsSimpleModule (MonoidAlgebra ℂ Γ) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let W' : Submodule (MonoidAlgebra ℂ Γ) τ.asModule :=
    { carrier := {x | τ.asModuleEquiv x ∈ W}
      add_mem' := fun {a b} ha hb => by
        show τ.asModuleEquiv (a + b) ∈ W
        rw [map_add (f := _)]
        exact W.add_mem ha hb
      zero_mem' := by
        show τ.asModuleEquiv 0 ∈ W
        rw [map_zero]
        exact W.zero_mem
      smul_mem' := fun r x hx => by
        show τ.asModuleEquiv (r • x) ∈ W
        rw [Representation.asModuleEquiv_map_smul]
        exact τ.asAlgebraHom_mem_of_forall_mem W hWinv _ hx r }
  have hW' : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hmem : τ.asModuleEquiv.symm w ∈ W' := by
      show τ.asModuleEquiv (τ.asModuleEquiv.symm w) ∈ W
      simpa using hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  have hsup : ∀ S : Submodule (MonoidAlgebra ℂ Γ) τ.asModule,
      (∀ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f ≤ S) → S = ⊤ := by
    intro S hS
    let S0 : Submodule ℂ V :=
      (S.restrictScalars ℂ).comap (τ.asModuleEquiv.symm : V →ₗ[ℂ] τ.asModule)
    have hS0 : S0 = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun f => ?_
      rintro _ ⟨x, rfl⟩
      let F : Representation.IntertwiningMap σ τ :=
        f.1.intertwiningMap_of_isIntertwiningMap σ τ f.2
      exact hS (Representation.IntertwiningMap.equivLinearMapAsModule σ τ F)
        ⟨σ.asModuleEquiv.symm x, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : τ.asModuleEquiv y ∈ S0 := hS0 ▸ Submodule.mem_top
    simpa [S0] using hy
  obtain ⟨g, hg, hgW⟩ := UpperTheory.Reformulated.B.SubgroupFixed.core hsup W' hW'
  refine ⟨τ.asModuleEquiv (g (σ.asModuleEquiv.symm x0)), hgW ⟨_, rfl⟩, ?_, ?_⟩
  · intro h0
    have h1 : g (σ.asModuleEquiv.symm x0) = 0 := by simpa using h0
    have h2 : σ.asModuleEquiv.symm x0 = 0 := hg (h1.trans (map_zero g).symm)
    exact hx0 (by simpa using h2)
  · intro u hu
    apply τ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply, ← map_smul,
      ← Representation.asModuleEquiv_symm_map_rho, hfix u hu]
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix

namespace UpperTheory.V.Af.GlobalFixedVectors

theorem sub_fixed {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, τ g v ∈ W) (h0 : W ≠ ⊥) (K : Subgroup Γ) (hK : HasFixed σ K) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ K, τ u v = v :=
  _root_.UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed σ hσ τ h W hW h0 K hK

variable {F : Type} [Field F] [NumberField F] {n M : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ ∀ w : HeightOneSpectrum (𝓞 F), pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem gl_ext {g h : GL (Fin n) (Af F)}
    (e : ∀ w, GeneralLinearGroup.map (pLoc F w) g = GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) (e w)

theorem pLoc_sLoc (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : pLoc F w (sLoc F w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w x

theorem pLoc_sLoc_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : w.adicCompletion F) : pLoc F v (sLoc F w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) h x

theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) {x : Af F} (hx : x ∈ Ohat F) : sLoc F w (pLoc F w x) ∈ Ohat F :=
  mem_Ohat.2 fun v => by
    by_cases h : v = w
    · subst h; rw [pLoc_sLoc]; exact mem_Ohat.1 hx v
    · rw [pLoc_sLoc_of_ne h]; exact zero_mem _

noncomputable def eLoc (w : HeightOneSpectrum (𝓞 F)) : Ohat F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w (pLoc F w x), sLoc_mem w x.2⟩
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem eLoc_eq (w : HeightOneSpectrum (𝓞 F)) (x : Ohat F) : eLoc w x = eLoc w 1 * x := by
  refine Subtype.ext (FiniteAdeleRing.ext _ fun v => ?_)
  change pLoc F v (sLoc F w (pLoc F w x)) = pLoc F v (sLoc F w (pLoc F w (1 : Ohat F)) * x)
  rw [map_mul]
  by_cases h : v = w
  · subst h; simp [pLoc_sLoc]
  · simp [pLoc_sLoc_of_ne h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) :
    GeneralLinearGroup.map (pLoc F w) k ∈ KLoc F w n M := by
  obtain ⟨g, hg, rfl⟩ := hk
  refine ⟨cornerGL n (eLoc w) g, ?_, ?_⟩
  · ext i j
    have h1 := congrArg (fun x : GL (Fin n) (Ohat F ⧸ Ideal.span {(M : ↥(Ohat F))}) => x i j) (MonoidHom.mem_ker.1 hg)
    change Ideal.Quotient.mk _ (g i j) = (1 : Matrix (Fin n) (Fin n) _) i j at h1
    change Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j -
      eLoc w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j) + eLoc w (g i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [eLoc_eq w (g i j), eLoc_eq w (_ : Ohat F)]
    simp [h1, Matrix.one_apply, apply_ite (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))]
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) -
      sLoc F w (pLoc F w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Ohat F)) + sLoc F w (pLoc F w (g i j)) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) +
        sLoc F w (pLoc F w (g i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem tendsto_of_loc {α : Type} {𝓕 : Filter α} {f : α → Af F} {x : Af F} (hx : x ∈ Ohat F) (hf : ∀ᶠ a in 𝓕, f a ∈ Ohat F)
    (h : ∀ w, ∀ᶠ a in 𝓕, pLoc F w (f a) = pLoc F w x) : Tendsto f 𝓕 (𝓝 x) := by
  classical
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : Af F → ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun y v => if h : y ∈ Ohat F then ⟨pLoc F v y, mem_Ohat.1 h v⟩ else ⟨0, zero_mem _⟩
  have hl : ∀ y ∈ Ohat F, s (lift y) = y := fun y hy => FiniteAdeleRing.ext _ fun v => by
    change ((lift y v : _) : v.adicCompletion F) = pLoc F v y
    simp [lift, hy]
  have h1 : Tendsto (fun a => lift (f a)) 𝓕 (𝓝 (lift x)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| by
      filter_upwards [hf, h v] with a ha hav
      simp [lift, ha, hx, hav]
  have h2 := (hs.tendsto _).comp h1
  rw [hl x hx] at h2
  exact h2.congr' (hf.mono fun a ha => hl _ ha)

theorem entry_mem {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) (i j : Fin n) : k i j ∈ Ohat F := by
  obtain ⟨g, -, rfl⟩ := hk
  exact (g i j).2


variable (n M) in
noncomputable def KAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GL (Fin n) (Af F)) :=
  KLev F n M ⊓ ⨅ w ∈ S, (GeneralLinearGroup.map (pLoc F w)).ker

theorem mem_KAway {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GL (Fin n) (Af F)} :
    k ∈ KAway n M S ↔ k ∈ KLev F n M ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc F w) k = 1 := by
  simp [KAway, Subgroup.mem_iInf]

theorem exists_KAway_subset {U : Set (GL (Fin n) (Af F))} (hU : U ∈ 𝓝 (1 : GL (Fin n) (Af F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (KAway n M S : Set (GL (Fin n) (Af F))) ⊆ U := by
  classical
  by_contra hn
  push Not at hn
  choose k hk hkU using fun S => Set.not_subset.1 (hn S)
  have ent : ∀ k : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin n) (Af F), (∀ S, k S ∈ KAway n M S) →
      Tendsto (fun S => (k S).val) atTop (𝓝 1) := fun k hk =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (entry_mem (one_mem (KLev F n M)) i j) (.of_forall fun S => entry_mem (mem_KAway.1 (hk S)).1 i j) fun w => by
        filter_upwards [eventually_ge_atTop {w}] with S hS
        have e := (mem_KAway.1 (hk S)).2 w (hS (Finset.mem_singleton_self w))
        rw [← map_one (GeneralLinearGroup.map (pLoc F w))] at e
        exact congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) e
  have ht : Tendsto k atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent k hk).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (ent (fun S => (k S)⁻¹) fun S => inv_mem (hk S)))
  obtain ⟨S, hS⟩ := (ht.eventually hU).exists
  exact hkU S hS

end UpperTheory.V.Af.GlobalFixedVectors
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ

theorem UpperTheory.V.Af.wdAway :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
end

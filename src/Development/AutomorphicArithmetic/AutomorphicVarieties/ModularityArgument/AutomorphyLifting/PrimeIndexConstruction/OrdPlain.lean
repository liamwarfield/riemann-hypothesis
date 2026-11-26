module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsOfForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FinProj
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

end UpperTheory.V.Sd.Wc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsPlain
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

theorem psPlain : PsPlain := by
  intro F _ _ w σ ψ hψ hs hl
  have key : ∀ x : (w.adicCompletion F)ˣ, ((absPow (w.adicCompletion F) 1 x : ℂˣ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (-ord (w.adicCompletion F) x) := fun x => by
    obtain ⟨h1, h2, -⟩ := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x
    rw [val_absPow, Complex.cpow_one, ← h1, h2]
    push_cast
    rfl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars σ.irred ψ hψ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    refine hl i j ⟨fun x hx => ?_, ?_⟩
    · have h3 := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x).2.2
      have h0 : ord (w.adicCompletion F) x = 0 := by
        have h4 : WithZero.exp (-ord (w.adicCompletion F) x) = WithZero.exp (0 : ℤ) :=
          h3.symm.trans (Eq.trans hx WithZero.exp_zero.symm)
        have := WithZero.exp_injective h4
        omega
      have h5 : absPow (w.adicCompletion F) 1 x = 1 := Units.ext (by rw [key, h0]; simp)
      rw [h, MonoidHom.mul_apply, h5, mul_one]
    · have h1 := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 (atFin w (unif w))
      have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
        unif_spec w
      have h0 : ord (w.adicCompletion F) (atFin w (unif w)) = 1 := by
        have := WithZero.exp_injective (h1.2.2.symm.trans h2)
        omega
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
        intro e
        have e' : ((normV w : ℕ) : ℝ) = 0 := by exact_mod_cast e
        have h6 := h1.2.1
        rw [h0, e'] at h6
        have h7 : ‖((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F)‖ ≠ 0 :=
          norm_ne_zero_iff.2 (Units.ne_zero _)
        exact h7 (by simpa using h6)
      rw [h, MonoidHom.mul_apply, Units.val_mul, key, h0, mul_assoc, zpow_neg_one, inv_mul_cancel₀ hq, mul_one]

end UpperTheory.V.Z.Win.Birth

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTransAlt
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd Matrix

namespace UpperTheory.V.Z.Win.Birth

private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : Pl F) : K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  have : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem scalar_fin {F : Type} [Field F] [NumberField F] (w : Pl F) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem hasU_of_map {F : Type} [Field F] [NumberField F] (w : Pl F) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {ρ' : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) W} (p : V →ₗ[ℂ] W) (hp : ∀ g y, p (ρ g y) = ρ' g (p y))
    {c : ℕ} {lam : ℂ} {x : V} (h0 : p x ≠ 0) (hx : x ∈ Hi.fixd ρ (K1 w c)) (hU : Uop w ρ c x = lam • x) :
    HasU w ρ' c lam := by
  obtain ⟨N, a, -, h⟩ := Wc.hkReps uopSum F w c
  have hx' : p x ∈ Hi.fixd ρ' (K1 w c) := fun u hu => by rw [← hp, hx u hu]
  refine ⟨p x, h0, hx', ?_⟩
  rw [(h W ρ' _ hx').2]
  have e := (h V ρ x hx).2
  rw [hU] at e
  have e2 := congrArg p e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum] at e2
  rw [e2]
  simp only [hp]

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx in
theorem _root_.UpperTheory.V.Z.Win.Birth.locTrans : LocTrans := by
  intro F _ _ _ π w
  let orb {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

  have orb_comm {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
      (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

  have orb_act {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
      orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
    | single a b => simp [orb]

  let annPart {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V := {
    carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
    add_mem' := fun {x y} hx hy c hc => by
      have : orb κ (x + y) c = orb κ x c + orb κ y c := by
        simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
      rw [this, hx c hc, hy c hc, add_zero]
    zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
    smul_mem' := fun a x hx c hc => by
      have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
      simpa [hx c hc] using this }

  have exists_type {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (φ : V)
      (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
      ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
        (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
    have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
      rintro k _ ⟨c, rfl⟩
      exact ⟨_, orb_act κ φ k c⟩
    have : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
      change FiniteDimensional ℂ (LinearMap.range (Finsupp.linearCombination ℂ fun k => κ k φ))
      rwa [Finsupp.range_linearCombination]
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

  have smooth_fin (π : TR.CuspSub F 2) : IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff

  have smooth_loc (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
    (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

  have cpt_fin (π : TR.CuspSub F 2) (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
      π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
    refine Subtype.ext ?_
    change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (finGL F 2 g)) y.1 =
      (TR.rt F 2 (finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, TR.infGL_comm]

  have fin_loc (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin 2) (Af F)}
      (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin 2) (w.adicCompletion F)) (y : π.V) :
      π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
    simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]

  have bot_or_top (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
      (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
      (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
          (π.finPart ((locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
          (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
      | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F 2 w g)) y.1)) x hx
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, hop o x hx, rfl⟩) with h | h
    · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

  have isotypic (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F)))
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

  let cptPart (π : TR.CuspSub F 2) : Representation ℂ (TR.Kinf F 2) π.V :=
    sub (TR.cptRep F 2) π.V fun k => π.stable (.cpt k)

  have exists_comp : ∃ σ, π.IsLocComp w σ := by
    obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    set φ : π.V := ⟨φ₀, hφ⟩
    have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
    set L := stab π.finPart φ
    have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := smooth_fin π _
    obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
      have := (π.cusp φ₀ hφ).1.kfin
      refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
        (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ₀)) fun v => ?_)
        fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
    have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
    let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
      fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin 2) (pLoc F w)).ker)
    obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
        rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
          (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
        · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
        · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
      U (fun g x hx => ⟨fun c hc => by
          rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
        mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
      ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
        obtain ⟨W, hW, hWf⟩ := admissibleReal F 2 π (L ⊓ (K' ⊓ L.comap (locGL F 2 w)).comap (GeneralLinearGroup.map (pLoc F w)))
          (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
            (continuous_map_pLoc w))) d ξ
        refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
        obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
        refine hWf f hf (fun k hk v => ?_) hx1
        have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
        have h2 := mem_fix.1 hx.2 _ hk.2.1
        have h3 : π.finPart k x = x := by
          rw [← mul_inv_cancel_left (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
            mul_apply_eq_comp, h1]
          exact h2
        obtain ⟨c, hc⟩ := hf2 v
        rw [hc, ← orb_comm _ _ (hcomm k), h3])
    exact ⟨σ, hσ⟩
  refine ⟨fun ⟨x, hx0, hx⟩ => ?_, fun σ hσ => ⟨fun c lam ⟨x, hx0, hx, hU⟩ => ?_, fun ω hω z v => ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_comp
    have hi := isotypic π w σ hσ
    have hxK : x ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w (n := 2)) :=
      GlobalTheory.LGrp.mem_fixed.2 (fun k hk => hx k (level_zero_eq_maximal_compact w ▸ hk))
    let maps := {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}
    obtain ⟨y, hy0, hy⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
      (fun f : maps => f.1) (fun f => f.2) _ x hx0 (GlobalTheory.LGrp.mem_fixed.1 hxK)
      (hi.2 ▸ Submodule.mem_top)
    obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    refine ⟨B, ⟨(Submodule.ne_bot_iff _).2 ⟨x, hxK, hx0⟩, fun v hv h0 => ?_⟩⟩
    exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB
      (fun f : maps => f.1) (fun f => f.2) (hi.2 ▸ Submodule.mem_top) hv h0
  · classical
    let τ := π.locRep w
    let maps := {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = τ g (f v)}
    have htop : ⨆ f : maps, LinearMap.range f.1 = ⊤ := (isotypic π w σ hσ).2
    let Fmap (f : maps) : σ.ρ.asModule →ₗ[MonoidAlgebra ℂ _] τ.asModule :=
      Representation.IntertwiningMap.equivLinearMapAsModule σ.ρ τ
        ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
    let Φ := Finsupp.lsum ℕ Fmap
    have hΦ : Function.Surjective Φ := fun y => by
      obtain ⟨v, rfl⟩ := τ.asModuleEquiv.symm.surjective y
      have hv : v ∈ ⨆ f : maps, LinearMap.range f.1 := htop ▸ Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun v => ∃ z, Φ z = τ.asModuleEquiv.symm v) hv ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact ⟨Finsupp.single f (σ.ρ.asModuleEquiv.symm v), Finsupp.lsum_single _ _ _ _⟩
      · exact ⟨0, (map_zero Φ).trans (map_zero τ.asModuleEquiv.symm).symm⟩
      · rintro a b ⟨z, hz⟩ ⟨z', hz'⟩
        exact ⟨z + z', by rw [map_add Φ, hz, hz', map_add τ.asModuleEquiv.symm]⟩
    have := σ.irred
    have := IsSemisimpleModule.of_surjective Φ hΦ
    obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property Φ hΦ (LinearMap.id : τ.asModule →ₗ[MonoidAlgebra ℂ _] τ.asModule)
    let x' := τ.asModuleEquiv.symm x
    have hsx : s x' ≠ 0 := by
      intro e
      have h := LinearMap.congr_fun hs x'
      change Φ (s x') = x' at h
      rw [e, map_zero] at h
      exact (map_ne_zero_iff _ τ.asModuleEquiv.symm.injective).2 hx0 h.symm
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hsx
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ.ρ).symm (Finsupp.lapply i ∘ₗ s)
    exact hasU_of_map w p.toLinearMap (fun g v => p.isIntertwining _ _ g v) hi hx hU
  · obtain ⟨f, h0, hf⟩ := hσ
    have hinj : LinearMap.ker f = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    refine LinearMap.ker_eq_bot.1 hinj ?_
    rw [hf, map_smul]
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f v).1.1 (g * finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) z))) = ((ω.loc w z : ℂˣ) : ℂ) * (f v).1.1 g
    rw [scalar_fin, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ (f v).2]
    rfl

end UpperTheory.V.Z.Win.Birth
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsCent
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

private theorem scalar_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (g : G) (c : ℂ) (hg : ∀ v, ρ g v = c • v) (w : W) :
    σ g w = c • w := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨s, rfl⟩ := hf w
  have h1 : S.toRepresentation g s = c • s := Subtype.ext (hg s.1)
  have h2 := f.isIntertwining _ _ g s
  rw [← h2, h1, map_smul]

private theorem prinSeries_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : Fin 2 → kˣ →* ℂˣ) (z : kˣ) (f) :
    prinSeries ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) f = ((ψ 0 z * ψ 1 z : ℂˣ) : ℂ) • f := by
  refine GlobalTheory.CompanionTheory.ZCentre.parInd_scalar _ _ z _ (fun w => ?_) f
  have h : (leviTorus k (Fin 2)).symm (fun a => Matrix.GeneralLinearGroup.scalar Unit z) = fun _ => z := by
    rw [MulEquiv.symm_apply_eq]
    funext a
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp [leviTorus, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal]
  show ofChar (torusChar ψ) ((leviTorus k (Fin 2)).symm fun a => Matrix.GeneralLinearGroup.scalar Unit z) w = _
  rw [h, ofChar_apply, torusChar_apply, Fin.prod_univ_two, smul_eq_mul]

theorem psCent : PsCent := by
  intro F _ _ w σ ψ h z v
  exact scalar_of_isSubquotient h _ _ (fun f => prinSeries_scalar ψ z f) v

end UpperTheory.V.Z.Win.Birth
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.DetCent
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open GlobalTheory.HeckeGal GlobalTheory.LFun GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary Formalism.UG UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd Polynomial Matrix

namespace UpperTheory.V.Z.Win.Birth

private theorem scalar_eq_prod {E V : Type} [Field E] [NumberField E] {a : ℕ} [AddCommGroup V] [Module ℂ V]
    {w : HeightOneSpectrum (𝓞 E)} {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {B : Multiset ℂˣ}
    (hB : HasSatGL w ρ B) {c : ℂˣ}
    (hc : ∀ x, ρ (GeneralLinearGroup.scalar (Fin a) (atFin w (unif w))) x = (c : ℂ) • x) : c = B.prod := by
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  set u : (w.adicCompletion E)ˣ := atFin w (unif w) with hu_def
  have hu : IsUnifV E w (u : w.adicCompletion E) := unif_spec w
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero
  have hTn : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a =
      dosetInd ℂ (KGL w (n := a)) (GlobalTheory.WeylGL.tor h0 fun _ => 1) := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hTn, heckeVec_dosetInd (R := {GlobalTheory.WeylGL.tor h0 fun _ => 1}) hx.2.1, Finset.sum_singleton] at h1
  rotate_left
  · intro γ hγ
    exact GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← GlobalTheory.WeylGL.tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd
  have ht : GlobalTheory.WeylGL.tor h0 (fun _ : Fin a => (1 : ℤ)) = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  rw [ht, hc] at h1
  have h3 : satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    have hcd : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
    rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    conv_lhs => rw [← hcd]
    rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [h3] at h1
  exact Units.ext (smul_left_injective ℂ hx.1 h1)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : HeightOneSpectrum (𝓞 F))
    (u : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u)) =
      GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) := by
  have hz : locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map (corner (sLoc F w)) u) := cornerGL_scalar _ u
  have hf : ∀ y, finGL F 2 (GeneralLinearGroup.scalar (Fin 2) y) = GeneralLinearGroup.scalar (Fin 2) (finId F y) :=
    fun y => cornerGL_scalar _ y
  have e1 := finId_det_locGL (E := F) (a := 1) w (GeneralLinearGroup.scalar (Fin 1) u)
  have e2 : GeneralLinearGroup.det (locGL F 1 w (GeneralLinearGroup.scalar (Fin 1) u)) =
      Units.map (corner (sLoc F w)) u := by
    rw [locGL, cornerGL_scalar]; ext; simp
  have e3 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by ext; simp
  rw [e2, e3] at e1
  rw [hz, hf, e1]

private theorem locRep_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (ω : HChar F)
    (hω : ∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (w : HeightOneSpectrum (𝓞 F)) (u : (w.adicCompletion F)ˣ) (x : π.V) :
    π.locRep w (GeneralLinearGroup.scalar (Fin 2) u) x = ((ω.loc w u : ℂˣ) : ℂ) • x := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have e : (π.locRep w (GeneralLinearGroup.scalar (Fin 2) u) x).1.1 g =
      x.1.1 (g * finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) u))) := rfl
  rw [e, fin_scalar, show g * GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) =
    GeneralLinearGroup.scalar (Fin 2) (localIdele F w u) * g from ?_, hω _ _ x.2]
  · rfl
  · ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]

private theorem absVal {F : Type} [Field F] [NumberField F] (t : ℤ) (v : HeightOneSpectrum (𝓞 F)) :
    (((GlobalTheory.HeckeGal.Model.absPow F (t : ℝ)).val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-t) := by
  rw [(GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (t : ℝ)).2.1 v]
  have e : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (normV v : ℂ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, ← Complex.cpow_intCast]
  push_cast
  rfl

private theorem fin_order {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ξ : G F Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G F Ω))) :
    Continuous ξ ∧ ∃ m : ℕ, 0 < m ∧ ξ ^ m = 1 := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  refine ⟨continuous_of_isOpen_ker' ξ h, ξ.ker.index, ?_, ?_⟩
  · haveI : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  · ext σ
    have := Subgroup.pow_index_mem ξ.ker σ
    simpa [MonoidHom.mem_ker] using congrArg Units.val (MonoidHom.mem_ker.1 this)

private theorem det_sat {M : Matrix (Fin 2) (Fin 2) ℂ} {q : ℕ} {B : Multiset ℂˣ} (hc : B.card = 2)
    (h : M.charpoly = ((algSat 2 q B).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((B.prod : ℂˣ) : ℂ) := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hc
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, Multiset.prod_pair,
    mul_mul_mul_comm, hq', Units.val_mul]

theorem detCent : DetCent := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s π r hatt hdet hker ω hω w
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨hξc, m, hm, hξm⟩ := fin_order ξ hker
  obtain ⟨χ, ⟨hχm, hχ⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hξc hm hξm
  set P : HChar F := GlobalTheory.HeckeGal.Model.absPow F ((s + 1 : ℤ) : ℝ) with hP
  have hfl : {v : HeightOneSpectrum (𝓞 F) | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : ((l : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 F)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hl' : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    Filter.eventually_cofinite.2 (by simpa using hfl)
  have hqne : ∀ v : HeightOneSpectrum (𝓞 F), (normV v : ℂ) ≠ 0 := fun v => by
    have h1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have h2 : 0 < normV v := by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using (zero_lt_one.trans h1)
    exact_mod_cast h2.ne'
  have hν : ω * χ⁻¹ * P⁻¹ = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1,
      hl'] with v ⟨B, hB, hF⟩ hu hl
    have hB' : HasSatGL v (π.locRep v) B := hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have e1 : ω.val v = B.prod := scalar_eq_prod hB' (fun x => locRep_scalar π ω hω v _ x)
    have hcard : B.card = 2 := by
      obtain ⟨x, hx⟩ := hB'.exists_vec
      exact hx.2.2.1
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_sat hcard e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (DFunLike.congr_fun hdet σ⁻¹)
    have e6 := hχ.frob_unr ha (Or.inr rfl) hu hA hσ
    have e7 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
      rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hl hA hσ]
      simp
    have h8 : ι ((ξ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val v : ℂˣ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, e6, inv_inv, ι.apply_symm_apply]
    have h9 : ι (((cycBar F Ω l ^ s) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV v : ℂ) ^ (-s) := by
      rw [MonoidHom.zpow_apply, map_inv, _root_.inv_zpow', Units.val_zpow_eq_zpow_val, e7, map_zpow₀, map_natCast]
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, map_mul, Matrix.GeneralLinearGroup.val_det_apply,
      h8, h9] at e5
    rw [e4, e3] at e5
    refine Units.ext ?_
    have h10 := absVal (F := F) (s + 1) v
    rw [HChar.val_mul, HChar.val_mul, HChar.val_inv, HChar.val_inv, Units.val_mul, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hP, h10, e1, Units.val_one]
    have hq := hqne v
    have hc : ((χ.val v : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    have hs : (normV v : ℂ) ^ (-s) ≠ 0 := zpow_ne_zero _ hq
    field_simp
    linear_combination e5
  have hωe : ω = χ * P := by
    rw [mul_assoc, ← mul_inv, mul_inv_eq_one] at hν
    exact hν
  refine ⟨⟨m, hm, ?_⟩, fun A hA hU => ?_⟩
  · have h1 : ω.loc w (atFin w (unif w)) = ω.val w := rfl
    have h2 : ((χ.val w : ℂˣ) : ℂ) ^ m = 1 := by
      have h3 : (χ ^ m).val w = χ.val w ^ m := MonoidHom.pow_apply χ.1 m _
      rw [show χ ^ m = 1 from hχm] at h3
      rw [← Units.val_pow_eq_pow_val, ← h3]
      rfl
    rw [h1, hωe, HChar.val_mul, Units.val_mul, hP, absVal, mul_assoc, ← zpow_add₀ (hqne w), neg_add_cancel, zpow_zero,
      mul_one, h2]
  · have hu : χ.UnrAt w := fun x hx => by
      have h1 := hU x hx
      rw [hωe] at h1
      change (χ.loc w) x * (P.loc w) x = 1 at h1
      rw [hP, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F _).1 w x hx, mul_one] at h1
      exact h1
    exact fun σ hσ => (hχ.unr_iff ha (Or.inr rfl) hA).2 hu σ hσ

end UpperTheory.V.Z.Win.Birth
end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

private theorem real_core (t L A B : ℝ) (m0 m1 s : ℤ) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : A * B * t ^ (s + 1) = 1) (h2 : L * t ^ m0 = 1) (h3 : L ^ 2 = t * A ^ 2)
    (h4 : A * t = B ∨ B * t = A) (h5 : m1 + 2 ≤ m0) (h6 : m0 + m1 = s) : False := by
  have hL : L ≠ 0 := by
    rintro rfl
    simp at h2
  have ht : t ≠ 0 := ht0.ne'
  have e0 : L ^ 2 * t ^ (2 * m0) = 1 := by
    have e : t ^ (2 * m0) = (t ^ m0) ^ 2 := by rw [two_mul, zpow_add₀ ht, sq]
    rw [e, ← mul_pow, h2, one_pow]
  have inj : ∀ a b : ℤ, L ^ 2 * t ^ a = 1 → L ^ 2 * t ^ b = 1 → a = b := by
    intro a b ha hb
    have e : t ^ a = t ^ b := mul_left_cancel₀ (pow_ne_zero 2 hL) (ha.trans hb.symm)
    exact zpow_right_injective₀ ht0 ht1.ne e
  rcases h4 with h4 | h4
  · subst h4
    have e : L ^ 2 * t ^ (s + 1) = 1 := by
      rw [h3]
      linear_combination h1
    have := inj _ _ e e0
    omega
  · subst h4
    have e1 : t ^ (s + 1) = t ^ (s - 1) * t ^ 2 := by
      rw [show s + 1 = (s - 1) + 2 by ring, zpow_add₀ ht]
      norm_cast
    have e : L ^ 2 * t ^ (s - 1) = 1 := by
      rw [e1] at h1
      rw [h3]
      linear_combination h1
    have := inj _ _ e e0
    omega

private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [hl : Fact l.Prime] (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : 0 < ‖(normV w : Qbar l)‖ ∧ ‖(normV w : Qbar l)‖ < 1 := by
  have e : normV w = Ideal.absNorm w.asIdeal := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h1 : 1 < normV w := by
    rw [e]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hd : l ∣ normV w := by
    have h2 : Ideal.absNorm w.asIdeal ∣ Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 F)}) :=
      Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
    rw [Ideal.absNorm_span_natCast, ← e] at h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 h2
    rw [hk]
    refine dvd_pow_self l ?_
    rintro rfl
    simp [hk] at h1
  refine ⟨norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega)), ?_⟩
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)

private theorem norm_of_near {K : Type} [NormedField K] [IsUltrametricDist K] {x a : K} (h : ‖x - a‖ < 1)
    (ha : ‖a‖ = 1) : ‖x‖ = 1 := by
  have e : x = (x - a) + a := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact h.ne), ha]
  exact max_eq_right h.le

private theorem fin2 : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

theorem ordPlain : OrdPlain := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h v σ hσ
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Af.Rn.centChar F π
  by_cases hc : c v = 0
  · exact Or.inr ((locTrans F π v).1 (h.sph v hc))
  refine Or.inl ?_
  obtain ⟨hU, hcent⟩ := (locTrans F π v).2 σ hσ
  have hcent' := hcent ω hω
  obtain ⟨hN, hI⟩ := detCent F Ω l ι ξ s π r h.att h.det h.ξ_open ω hω v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨x, hx⟩ : ∃ x : σ.V, x ≠ 0 := by
    obtain ⟨f, hf, -⟩ := hσ
    obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hf
    refine ⟨y, ?_⟩
    rintro rfl
    simp at hy
  have hq1 : 1 < normV v := by
    have e : normV v = Ideal.absNorm v.asIdeal := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [e]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlam : ∃ lam : ℂ, HasU v (π.locRep v) (c v) lam ∧ lam ≠ 0 ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ‖ι.symm lam‖ * ‖(normV v : Qbar l)‖ ^ m v 0 = 1 ∧ m v 1 + 2 ≤ m v 0 ∧ m v 0 + m v 1 = s) := by
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨hc1, h12, hs, ha, ⟨lam, hlU, hnear⟩, -⟩ := h.above v hl
      have e := norm_of_near hnear ha
      have hn : ‖ι.symm lam‖ * ‖(normV v : Qbar l)‖ ^ m v 0 = 1 := by
        rw [← norm_zpow, ← norm_mul]
        exact e
      refine ⟨lam, hc1 ▸ hlU, ?_, fun _ => ⟨hn, h12, hs⟩⟩
      rintro rfl
      simp at hn
    · obtain ⟨lam, hlU, hn⟩ := h.away v hc hl
      refine ⟨lam, hlU, ?_, fun h' => absurd h' hl⟩
      rintro rfl
      simp at hn
  obtain ⟨lam, hlU, hl0, hln⟩ := hlam
  obtain ⟨ψ, hsm, hsub, hun, hsq⟩ := uLoc F v (c v) lam σ hc hl0 ((hU _ _) hlU)
  have hprod : ∀ z, ψ 0 z * ψ 1 z = ω.loc v z := by
    intro z
    have e := (psCent F v σ ψ hsub z x).symm.trans (hcent' z x)
    exact Units.ext (smul_left_injective ℂ hx e)
  refine psPlain F v σ ψ hsm hsub ?_
  rintro i j ⟨hu, hq⟩
  by_cases hij : i = j
  · subst hij
    have h0 : ((ψ i (atFin v (unif v)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have e : ((normV v : ℕ) : ℂ) = 1 := mul_left_cancel₀ h0 (by rw [hq, mul_one])
    have e' : normV v = 1 := by exact_mod_cast e
    omega
  have hu01 : ∀ y, IsUnitAt v y → ψ 1 y = 1 := by
    intro y hy
    rcases fin2 i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hu y hy, hun y hy]
    · rw [hu y hy, hun y hy]
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · obtain ⟨hn, h12, hs⟩ := hln hl
    obtain ⟨ht0, ht1⟩ := norm_q (l := l) v hl
    obtain ⟨N, hN0, hNe⟩ := hN
    have hnorm : ∀ z w : ℂ, ‖ι.symm (z * w)‖ = ‖ι.symm z‖ * ‖ι.symm w‖ := fun z w => by
      rw [map_mul, norm_mul]
    have hqn : ‖ι.symm ((normV v : ℕ) : ℂ)‖ = ‖(normV v : Qbar l)‖ := by rw [map_natCast]
    refine (real_core ‖(normV v : Qbar l)‖ ‖ι.symm lam‖ ‖ι.symm ((ψ 0 (atFin v (unif v)) : ℂˣ) : ℂ)‖
      ‖ι.symm ((ψ 1 (atFin v (unif v)) : ℂˣ) : ℂ)‖ (m v 0) (m v 1) s ht0 ht1 ?_ hn ?_ ?_ h12 hs).elim
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hNe
      simp only [map_pow, norm_pow, map_one, norm_one] at e
      have e2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0.ne').1 e
      rw [hnorm, ← hprod, Units.val_mul, hnorm, map_zpow₀, norm_zpow, hqn] at e2
      exact e2
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hsq
      simp only [map_pow, norm_pow, map_mul, norm_mul, map_natCast] at e
      exact e
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hq
      simp only [hnorm, hqn] at e
      rcases fin2 i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl e
      · exact Or.inr e
  · have hram : Ine (F := F) A ≤ ξ.ker := hI A hA (fun y hy => by
      rw [← hprod, hun y hy, hu01 y hy, one_mul])
    rcases (h.ram v A hA).1 hram with h0 | h0
    · exact absurd h0 hc
    · exact absurd h0 hl

end UpperTheory.V.Z.Win.Birth

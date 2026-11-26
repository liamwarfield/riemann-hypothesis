module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsRes
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private def locS {L : Type} (F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (b : 𝓞 L) : Subring F where
  carrier := {x | ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F x ≤ 1}
  one_mem' := fun P _ => by simp
  zero_mem' := fun P _ => by simp
  mul_mem' := fun {x y} hx hy P hP => by
    rw [map_mul]; exact mul_le_one' (hx P hP) (hy P hP)
  add_mem' := fun {x y} hx hy P hP => Valuation.map_add_le _ (hx P hP) (hy P hP)
  neg_mem' := fun {x} hx P hP => by rw [Valuation.map_neg]; exact hx P hP

private theorem exists_res {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {k : Type} [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L) (hb : r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0) (σ : F ≃ₐ[L] F) :
    ∃ ρ : locS F b →+* k, ∀ x : locS F b, ResF r (σ x) (ρ x) := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
  obtain ⟨a1, a2, a3, a4, -⟩ := UpperTheory.V.ZK.Cl.cAct L F
  have hex : ∀ x : locS F b, ∃ u, ResF r (σ x) u := by
    intro x
    refine ((h4 b hb).1 (σ x) fun P hP => ?_).2
    have e : P = actP σ (actP σ⁻¹ P) := by rw [← a2, mul_inv_cancel, a3]
    rw [e, a1]
    exact x.2 _ (by rwa [a4])
  choose f hf using hex
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · refine h1 _ _ _ (hf 1) ?_
    simpa using h2 1
  · intro x y
    refine h1 _ _ _ (hf (x * y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).2
  · refine h1 _ _ _ (hf 0) ?_
    simpa using h2 0
  · intro x y
    refine h1 _ _ _ (hf (x + y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).1

private theorem exists_mat {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {I : Type} [Fintype I] [DecidableEq I] (b : 𝓞 L) (g : (I → F) →ₗ[F] (I → F))
    (hg : ∀ x, InLoc b x → InLoc b (g x)) :
    ∃ A : Matrix I I (locS F b), (locS F b).subtype.mapMatrix A = LinearMap.toMatrix' g := by
  refine ⟨fun i j => ⟨g (Pi.single j 1) i, hg _ (fun i' P _ => ?_) i⟩, ?_⟩
  · by_cases h : i' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl

theorem UpperTheory.V.ZK.Cl.cMat :
    UpperTheory.V.ZK.Cl.CMat := by
  intro L F _ _ _ _ _ I _ k _ r b hb g hg
  classical
  obtain ⟨A, hA⟩ := exists_mat b (g : (I → F) →ₗ[F] (I → F)) fun x hx => (hg x).1 hx
  obtain ⟨B, hB⟩ := exists_mat b (g.symm : (I → F) →ₗ[F] (I → F)) fun x hx =>
    (hg _).2 (by simpa using hx)
  have hinj : Function.Injective ((locS F b).subtype.mapMatrix : Matrix I I (locS F b) → Matrix I I F) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hdet : ((LinearEquiv.det g : Fˣ) : F) = (A.det : locS F b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← hA, ← RingHom.map_det]
    rfl
  refine ⟨fun P hP => ?_, fun σ => ?_⟩
  · have h1 : ((A.det : locS F b) : F) * (B.det : locS F b) = 1 := by
      rw [← Subring.coe_mul, ← Matrix.det_mul, hAB]; simp
    have h2 := congrArg (P.valuation F) h1
    rw [map_mul, map_one] at h2
    have h3 : P.valuation F ((A.det : locS F b) : F) = 1 :=
      le_antisymm (A.det.2 P hP) (h2.symm.le.trans (mul_le_of_le_one_right' (B.det.2 P hP)))
    rw [ordP, hdet, h3]; simp
  · obtain ⟨ρ, hρ⟩ := exists_res r b hb σ
    obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
    refine ⟨Matrix.toLin'OfInv (M := ρ.mapMatrix B) (M' := ρ.mapMatrix A)
      (by rw [← map_mul, hBA, map_one]) (by rw [← map_mul, hAB, map_one]), ?_, fun w u hw hu i => ?_⟩
    · have := hρ A.det
      rw [← hdet, RingHom.map_det, ← LinearMap.det_toLin'] at this
      unfold Res
      rw [LinearEquiv.coe_det]
      exact this
    · let w' : I → locS F b := fun i => ⟨w i, hw i⟩
      have e1 : u = fun i => ρ (w' i) := funext fun i => h1 _ _ _ (hu i) (hρ (w' i))
      have e2 : g w i = (A.mulVec w' i : locS F b) := by
        have : g w = Matrix.mulVec (LinearMap.toMatrix' (g : (I → F) →ₗ[F] (I → F))) w := by
          simp
        rw [this, ← hA]
        exact (RingHom.map_mulVec (locS F b).subtype A w' i).symm
      have := hρ (A.mulVec w' i)
      rw [← e2, RingHom.map_mulVec] at this
      rw [e1]
      exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockVal
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

noncomputable section

namespace UpperTheory.V.ZK.Cl.BlockValuationRep

private theorem cyc_cm {A : Type} [CommRing A] {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Ch A G (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  rw [Cyc, (sChain A).2.1, show bd A G m z = 0 from hz, map_zero]

private def piRep {k : Type} [Field k] {G : Type} [Group G] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (ρ : ∀ b, G →* (U b ≃ₗ[k] U b)) : G →* ((∀ b, U b) ≃ₗ[k] ∀ b, U b) where
  toFun g := LinearEquiv.piCongrRight fun b => ρ b g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private def blk {k : Type} [Field k] {C : Type} [Group C] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (χ : B → C →* kˣ) (b : B) : (C × ∀ b, U b ≃ₗ[k] U b) →* (U b ≃ₗ[k] U b) where
  toFun p := scal (U b) (χ b p.1) * p.2 b
  map_one' := by simp
  map_mul' p p' := by
    ext w
    simp [scal, Units.smul_def, smul_smul, mul_comm]

private theorem pi_add {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} (hθ : IsAdd θ)
    {G : Type} [Group G] {z : Ch A G (m + 1)} (hz : Cyc z) (B : Type) [Fintype B] :
    ∀ (U : B → Type) [∀ b, AddCommGroup (U b)] [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z) := by
  refine Fintype.induction_empty_option (P := fun B _ => ∀ (U : B → Type) [∀ b, AddCommGroup (U b)]
      [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z)) ?_ ?_ ?_ B
  · intro α β _ e ih U _ _ _ V _ _ _ φ ρ ρ' h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← e.sum_comp]
    exact ih (fun a => U (e a)) V (φ.trans (LinearEquiv.piCongrLeft k U e).symm) ρ (fun a => ρ' (e a))
      fun g w a => h g w (e a)
  · intro U _ _ _ V _ _ _ φ ρ ρ' h
    haveI : Subsingleton V := φ.toEquiv.subsingleton
    haveI : Subsingleton (V ≃ₗ[k] V) := ⟨fun a b => LinearEquiv.ext fun _ => Subsingleton.elim _ _⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact hθ.bdry V _ ((sChain A).2.2.2.2 _ m _ (cyc_cm ρ hz))
  · intro α _ ih U _ _ _ V _ _ _ φ ρ ρ' h
    let ψ : V ≃ₗ[k] (U none × ∀ a, U (some a)) := φ.trans (LinearEquiv.piOptionEquivProd k)
    have hψ : (cj ψ).comp ρ = sumRep (ρ' none) (piRep (fun a => U (some a)) fun a => ρ' (some a)) := by
      refine MonoidHom.ext fun g => LinearEquiv.ext fun y => ?_
      obtain ⟨w, rfl⟩ := ψ.surjective y
      change ψ (ρ g (ψ.symm (ψ w))) = _
      rw [ψ.symm_apply_apply]
      exact Prod.ext (h g w none) (funext fun a => h g w (some a))
    rw [Fintype.sum_option, ← hθ.iso V _ ψ _ (cyc_cm ρ hz), ← (sChain A).2.2.1, hψ, hθ.add _ _ _ _ _ _ hz,
      ih (fun a => U (some a)) _ (LinearEquiv.refl k _) _ (fun a => ρ' (some a)) fun _ _ _ => rfl]

end UpperTheory.V.ZK.Cl.BlockValuationRep

open UpperTheory.V.ZK.Cl.BlockValuationRep in
theorem UpperTheory.V.ZK.Cl.cBlockVal :
    UpperTheory.V.ZK.Cl.CBlockVal := by
  unfold UpperTheory.V.ZK.Cl.CBlockVal
  intro k _ q _ e ζ hζ v θ hθ hv B _ U _ _ _ V _ _ _ φ σ g x g' hσ hg
  obtain ⟨-, -, h2, h3, -⟩ := sChain (ZMod q)
  let χ : B → Cq q →* kˣ := fun b => chi q ζ hζ (x b)
  let R : (Cq q × ∀ b, U b ≃ₗ[k] U b) →* (V ≃ₗ[k] V) := (cj φ.symm).comp (piRep U (blk U χ))
  have hR : ∀ p w b, φ (R p w) b = blk U χ b p (φ w b) := by
    intro p w b
    simp [R, cj, piRep]
  have hRg : R (1, g') = g := by
    refine LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hR, hg]
    simp [blk]
  have hRσ : R.comp (MonoidHom.inl _ _) = σ := by
    refine MonoidHom.ext fun c => LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hσ, MonoidHom.comp_apply, MonoidHom.inl_apply, hR]
    simp [blk, scal, Units.smul_def, χ]
  have hblk : ∀ b, (blk U χ b).comp (MonoidHom.inl _ _) = (scal (U b)).comp (χ b) := by
    intro b
    refine MonoidHom.ext fun c => ?_
    simp [blk]
  have hk0 : ∀ b, blk U χ b (1, g') = g' b := by
    intro b
    simp [blk]
  have hy : Cyc (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) :=
    cyc_cm _ (sZc q e)
  have hconj : (MulAut.conj ((1 : Cq q), g')⁻¹).toMonoidHom.comp (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) =
      MonoidHom.inl _ _ := by
    refine MonoidHom.ext fun c => ?_
    simp
  have hZ : Cyc (prism (ZMod q) ((1 : Cq q), g') (2 * e + 1 + 1)
      (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))) := by
    show bd _ _ (2 * e + 1 + 1) _ = 0
    have s := sPrism (ZMod q) _ ((1 : Cq q), g') (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))
    have hy' : bd (ZMod q) _ (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) = 0 := hy
    rw [hy', map_zero, add_zero, ← h2, hconj, sub_self] at s
    exact s
  show θ V (prism (ZMod q) g (2 * e + 1 + 1) (cm (ZMod q) σ (2 * e + 1 + 1) (zc q e))) = _
  rw [← hRg, ← hRσ, h2, ← h3]
  refine (pi_add hθ hZ B U V φ R (blk U χ) hR).trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [h3, ← h2, hblk b, hk0 b]
  exact hv (U b) (x b) (g' b)

end
end

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private def blkEquiv {k Γ J X : Type} [Field k] [Group Γ] (s : J → Γ) (β : J → X) :
    (Γ × J → k) ≃ₗ[k] ∀ p : Γ × X, ({j // β j = p.2} → k) where
  toFun v p j := v (p.1 * s j.1, j.1)
  invFun w p := w (p.1 * (s p.2)⁻¹, β p.2) ⟨p.2, rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by ext p; simp
  right_inv w := by
    ext ⟨a, x⟩ ⟨j, hj⟩
    dsimp only at hj ⊢
    subst hj
    have key : ∀ a' : Γ, a' = a → w (a', β j) ⟨j, rfl⟩ = w (a, β j) ⟨j, rfl⟩ := by rintro _ rfl; rfl
    exact key _ (by simp)

theorem UpperTheory.V.ZK.Cl.cVal :
    UpperTheory.V.ZK.Cl.CVal := by
  intro L F _ _ _ _ _ J _ q _ e ζ h kap hkap k _ _ r b hb hS μ hμ hζ v θ hθ hv f hf χ 𝔟 δ g ρ ⟨_, s, β, g', hB, hs, hδ⟩ hρ
  classical
  obtain ⟨q1, q2, q3, -⟩ := cRes L F k r
  have hloc := ((cBlock L F J _ s β g').2 g.1 hB).2.1 b g.2
  choose g₁ hg₁ hg₂ using fun (x : ZMod q) => (cMat L F _ k r b hb (g' x) (hloc x)).2
  have hint : ∀ (I : Type) (a : I → 𝓞 F), InLoc b fun i => (a i : F) := fun I a i P _ => P.valuation_le_one (a i)
  have hlift : ∀ w : (F ≃ₐ[L] F) × J → k, ∃ a : J → 𝓞 F, ∀ σ j, r (actO σ (a j)) = w (σ, j) := fun w => by
    choose a ha using fun j => hS.1 fun σ => w (σ, j)
    exact ⟨a, fun σ j => ha j σ⟩
  have hred : ∀ (σ : F ≃ₐ[L] F) (a : 𝓞 F), ResF r (σ a) (r (actO σ a)) := fun σ a => q2 (actO σ a)
  rw [cBlockVal k q e _ hζ v θ hθ hv ((F ≃ₐ[L] F) × ZMod q) (fun p => {j // β j = p.2} → k) _ (blkEquiv s β) (μ.comp ρ) (μ g)
    (fun p => kap p.1 * p.2.val) (fun p => g₁ p.2 p.1), Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun x _ => ?_
    rw [← hδ, hf _ _ (hg₁ x σ)]
    simp
  · rintro c w ⟨σ, x⟩
    obtain ⟨a, ha⟩ := hlift w
    ext ⟨j, hj⟩
    dsimp only at hj
    have h1 := hμ (ρ c) _ w (hint J a) (fun τ j => ha τ j ▸ hred τ (a j)) (σ * s j) j
    refine q1 _ _ _ h1 ?_
    have h2 : (σ * s j) ((ρ c).1 (fun i => (a i : F)) j) =
        ((ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) : (𝓞 F)ˣ) : 𝓞 F) * (σ * s j) (a j) := by
      rw [hρ]
      change (σ * s j) (((toF ζ ^ ((χ j).val * (Multiplicative.toAdd c).val) : Fˣ) : F) * a j) = _
      rw [map_mul]
      congr 1
      have h3 : actU σ (actU (s j) (toF ζ ^ ((χ j).val * (Multiplicative.toAdd c).val))) =
          toF ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) := by
        rw [pow_mul, map_pow, map_pow (actU (s j)), hs, hj, map_pow, map_pow, hkap, pow_mul, pow_mul]
      have h4 := congrArg Units.val h3
      simpa [actU, toF] using h4
    rw [h2]
    have h5 := (q3 _ _ _ _ (q2 ((ζ ^ (kap σ * x.val * (Multiplicative.toAdd c).val) : (𝓞 F)ˣ) : 𝓞 F))
      (hred (σ * s j) (a j))).2
    rw [ha] at h5
    convert h5 using 1
    simp [chi, blkEquiv]
  · rintro w ⟨σ, x⟩
    obtain ⟨a, ha⟩ := hlift w
    ext ⟨j, hj⟩
    dsimp only at hj
    subst hj
    have h1 := hμ g _ w (hint J a) (fun τ j => ha τ j ▸ hred τ (a j)) (σ * s j) j
    refine q1 _ _ _ h1 ?_
    rw [AlgEquiv.mul_apply, hB]
    exact hg₂ (β j) σ _ _ (hint _ fun i : {i // β i = β j} => actO (s i.1) (a i.1))
      (fun i => by
        have := hred (σ * s i.1) (a i.1)
        rw [ha] at this
        exact this) ⟨j, rfl⟩

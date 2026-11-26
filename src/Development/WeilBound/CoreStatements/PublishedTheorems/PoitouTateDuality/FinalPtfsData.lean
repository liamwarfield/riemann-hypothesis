module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

structure FoundData (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (l r : ℕ) [Fact l.Prime] (ζ : AlgebraicClosure ℚ)
    (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M) where
  e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
    galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
    (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
    ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
        AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)
  ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 Kf.1))), AlgebraicClosure ℚ →ₐ[Kf.1]
    AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
  ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) (Av v)
  hev_cont : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm
  hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
    gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ
  hιs : ∀ (v : S) σ x, ιs ⟨v.1, Finset.mem_coe.2 v.2⟩
    (((ev v σ : Dec (F := Kf.1) (Av v)) : G Kf.1 (AlgebraicClosure ℚ)) x) =
      σ (ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ x)
  A : Rep.{0} (ULift.{0} ℤ)
    (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
  isDiscrete : IsDiscreteRep A
  eM : M ≃+ A.V
  hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)
  eD : TDual (ZMod (l ^ r)) M ≃+
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V
  hD : ∀ g f, eD (twDual μ ρ g f) =
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)
  hDζ : ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
        (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
          AlgebraicClosure ℚ) = ζ ^ (f m).val

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsKummer
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_kummer' (F : Type) [Field F] [NumberField F] {l r : ℕ} [Fact l.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra F (AlgebraicClosure ℚ)]
    [IsAlgClosure F (AlgebraicClosure ℚ)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (a : F) (ha : a ≠ 0)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap F (AlgebraicClosure ℚ) a) :
    ∃ κ : Dec (F := F) A → ZMod (l ^ r),
      (∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y) ∧
      Continuous κ ∧
      ∀ g h : Dec (F := F) A, κ (g * h) =
        κ g + ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) * κ h := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero r (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hN0⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at hy
    exact ha ((algebraMap F (AlgebraicClosure ℚ)).injective (by rw [← hy, map_zero]))

  have hroot : ∀ σ : G F (AlgebraicClosure ℚ), (σ y / y) ^ (l ^ r) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy, div_self (pow_ne_zero _ hy0)]
  have hex : ∀ σ : G F (AlgebraicClosure ℚ), ∃ i < l ^ r, ζ ^ i = σ y / y := fun σ => hζ.eq_pow_of_pow_eq_one (hroot σ)
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ a ≡ b [MOD l ^ r] := by
    intro a b
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ r) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    have e : ζ ^ a = ζ ^ b ↔ (hζ.isUnit hN0).unit ^ a = (hζ.isUnit hN0).unit ^ b := by
      rw [Units.ext_iff]; simp
    rw [e, pow_eq_pow_iff_modEq, ← hu.eq_orderOf]

  have huniq : ∀ a b : ℕ, ζ ^ a * y = ζ ^ b * y → (a : ZMod (l ^ r)) = b := by
    intro a b h
    have h' : ζ ^ a = ζ ^ b := mul_right_cancel₀ hy0 h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hmod a b).mp h')
  let κ : Dec (F := F) A → ZMod (l ^ r) := fun g => ((hex (g : G F (AlgebraicClosure ℚ))).choose : ZMod (l ^ r))
  have hκ : ∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y := by
    intro g
    have h1 := (hex (g : G F (AlgebraicClosure ℚ))).choose_spec
    have hv : (κ g).val = (hex (g : G F (AlgebraicClosure ℚ))).choose := ZMod.val_cast_of_lt h1.1
    rw [hv, h1.2, div_mul_cancel₀ _ hy0]
  have hκ_iff : ∀ (g : Dec (F := F) A) (b : ZMod (l ^ r)),
      κ g = b ↔ (g : G F (AlgebraicClosure ℚ)) y = ζ ^ b.val * y := by
    intro g b
    constructor
    · rintro rfl; exact hκ g
    · intro h
      have := huniq _ _ ((hκ g).symm.trans h)
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have : Algebra.IsIntegral F (AlgebraicClosure ℚ) := by
    have : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := IsAlgClosure.isAlgebraic
    infer_instance
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [continuous_discrete_rng]
    intro b
    have hset : κ ⁻¹' {b} = Subtype.val ⁻¹' {τ : G F (AlgebraicClosure ℚ) | τ y = ζ ^ b.val * y} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact hκ_iff g b
    rw [hset]
    exact (isOpen_setOf_apply (F := F) y (fun z => z = ζ ^ b.val * y)).preimage continuous_subtype_val
  · intro g h
    set c := ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) with hc
    have hgζ : (g : G F (AlgebraicClosure ℚ)) ζ = ζ ^ c.val := by
      have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
        (MulSemiringAction.toRingAut (G F (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (g : G F (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one
      exact hspec.trans (by rw [hc]; rfl)
    rw [hκ_iff]
    have e1 : ((g * h : Dec (F := F) A) : G F (AlgebraicClosure ℚ)) y = (g : G F (AlgebraicClosure ℚ)) ((h : G F (AlgebraicClosure ℚ)) y) := rfl
    rw [e1, hκ h, map_mul, map_pow, hgζ, hκ g, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
    apply (hmod _ _).mpr
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsHasse
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Hasse

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem urChar_mul (N : ℕ+) (g h : Gal(Ω/K)) :
    urChar K Ω N (g * h) = urChar K Ω N g + urChar K Ω N h := by
  simp only [urChar, map_mul, toAdd_mul, map_add (f := _)]

theorem urChar_one (N : ℕ+) : urChar K Ω N 1 = 0 := by
  simp only [urChar, map_one, toAdd_one, map_zero]

theorem urChar_of_ker (N : ℕ+) {g : Gal(Ω/K)} (hg : unramifiedDegree K Ω g = 1) :
    urChar K Ω N g = 0 := by
  simp only [urChar, hg, toAdd_one, map_zero]

theorem urChar_of_deg_one (N : ℕ+) {g : Gal(Ω/K)}
    (hg : unramifiedDegree K Ω g = Multiplicative.ofAdd 1) : urChar K Ω N g = 1 := by
  simp only [urChar, hg, toAdd_ofAdd, map_one]

theorem continuous_urChar (N : ℕ+) : Continuous (urChar K Ω N) :=
  continuous_unramifiedCoord (K := K) (Ω := Ω) N

def urPsi (N : ℕ+) : Additive Gal(Ω/K) →ₜ+ QZ where
  toFun a := zmodToQZ (N : ℕ) (urChar K Ω N (Additive.toMul a))
  map_zero' := by simp only [toMul_zero, urChar_one, map_zero]
  map_add' a b := by simp only [toMul_add, urChar_mul, map_add (f := _)]
  continuous_toFun :=
    (continuous_of_discreteTopology.comp (continuous_urChar (K := K) (Ω := Ω) N)).comp
      continuous_toMul

theorem reprIco_urPsi (N : ℕ+) (g : Gal(Ω/K)) :
    reprIco (charAdd (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g)) =
      ((urChar K Ω N g).val : ℚ) / (N : ℕ) := by
  rw [charAdd_apply]
  have h1 : (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) =
      QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ)) := by
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = _
    conv_lhs => rw [← ZMod.intCast_zmod_cast (urChar K Ω N g)]
    rw [zmodToQZ_intCast, ZMod.cast_eq_val]
    push_cast
    rfl
  rw [h1]
  have h2 : QZ.toAddCircle (QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ))) =
      ((((urChar K Ω N g).val : ℚ) / (N : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
    simp [QZ.mk]
  rw [h2, reprIco_coe]
  have hN : (0 : ℚ) < (N : ℕ) := by exact_mod_cast N.pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hN]
  exact_mod_cast ZMod.val_lt (urChar K Ω N g)

theorem charCocycle_urPsi (N : ℕ+) (g h : Gal(Ω/K)) :
    ((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) =
      ((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val := by
  have e := charCocycle_cast (charAdd (urPsi (K := K) (Ω := Ω) N)) g h
  rw [reprIco_urPsi, reprIco_urPsi, reprIco_urPsi] at e
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
  have : (((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) : ℚ) =
      (((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val : ℤ) := by
    push_cast
    rw [e]
    field_simp
  exact_mod_cast this

end Hasse

section HasseC

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem brauerInv_galCupClass_urPsi (N : ℕ+) (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) :
    brauerInvZOfIsSepClosure K Ω (galCupClass K Ω (urPsi (K := K) (Ω := Ω) N) ϖ) =
      zmodToQZ (N : ℕ) 1 := by
  obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  have hψ : ∀ g ∈ (unramifiedDegree K Ω).ker,
      (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) = 0 := by
    intro g hg
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = 0
    rw [urChar_of_ker N (MonoidHom.mem_ker.1 hg), map_zero]
  have key := brauerInvZ_galCupClass_of_unramified (urPsi (K := K) (Ω := Ω) N) hψ hσ ϖ
  show brauerInvZ K Ω _ = _
  rw [key, hϖ, one_smul]
  show zmodToQZ (N : ℕ) (urChar K Ω N σ) = _
  rw [urChar_of_deg_one N hσ]

end HasseC

section HasseMain

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem hasse_kummer_unram' (N : ℕ+)
    (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) (Y : Ω) (hY : Y ^ (N : ℕ) = algebraMap K Ω ϖ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ N) (κ : Gal(Ω/K) → ZMod (N : ℕ))
    (hκ : ∀ g : Gal(Ω/K), g Y = ζ ^ (κ g).val * Y)
    (c : cocycles (galUnitsZ K Ω) 2)
    (hc : ∀ s : Fin 2 → Gal(Ω/K), ((Additive.toMul (cochainOf _ (cocycleι _ 2 c) s) : Ωˣ) : Ω) =
      ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val) :
    brauerInvZOfIsSepClosure K Ω (cohomologyπ _ 2 c) = - zmodToQZ (N : ℕ) 1 := by
  classical
  have hN0 : (N : ℕ) ≠ 0 := N.ne_zero
  have hϖ0 : algebraMap K Ω (ϖ : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K Ω).injective).2 ϖ.ne_zero
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hY
    exact hϖ0 hY.symm
  let ψ := urPsi (K := K) (Ω := Ω) N
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω ϖ)
  let Yu : Ωˣ := Units.mk0 Y hY0
  let bf : Gal(Ω/K) → (galUnitsZ K Ω).V := fun h =>
    Additive.ofMul (Yu ^ (urChar K Ω N h).val)
  have hbf_lc : IsLocallyConstant fun t : Fin 1 → Gal(Ω/K) => bf (t 0) := by
    have h1 : IsLocallyConstant (urChar K Ω N) :=
      (IsLocallyConstant.iff_continuous _).2 (continuous_urChar (K := K) (Ω := Ω) N)
    exact (h1.comp fun u => Additive.ofMul (Yu ^ u.val)).comp_continuous (continuous_apply 0)
  have hsum : cohomologyπ _ 2 c + cohomologyπ _ 2 w = 0 := by
    rw [← map_add (f := _)]
    refine (PositivityTheory.LocalTateOrthogonality.Gcoh.pi_succ_eq_zero_iff (galUnitsZ K Ω) 1 (c + w)).2
      ⟨fun t => bf (t 0), hbf_lc, ?_⟩
    have hd := PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (galUnitsZ K Ω).ρ (galUnitsZ K Ω) (AddEquiv.refl _)
      (fun _ _ => rfl) 1 (fun t => bf (t 0))
    simp only [AddEquiv.refl_apply] at hd
    rw [hd]
    funext s
    rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_one, map_add (f := _), cochainOf_add, Pi.add_apply]
    have hwc' := hwc s
    have hc' := hc s
    set a0 := (urChar K Ω N (s 0)).val with ha0
    set a1 := (urChar K Ω N (s 1)).val with ha1
    set a01 := (urChar K Ω N (s 0 * s 1)).val with ha01
    set cc := charCocycle (charAdd ψ) (s 0, s 1) with hcc
    have hrel : ((N : ℕ) : ℤ) * cc = (a0 : ℤ) + a1 - a01 := charCocycle_urPsi N (s 0) (s 1)
    apply Additive.toMul.injective
    apply Units.ext
    rw [hwc']
    simp only [toMul_add, toMul_sub, toMul_zsmul, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_zpow_eq_zpow_val, bf]
    rw [hc', coe_unitsInvariant]
    have hL : ((Additive.toMul (((zRepOfMonoidEnd (galUnitsHom K Ω)) (s 0))
          (Additive.ofMul (Yu ^ (urChar K Ω N (s 1)).val)) -
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0 * s 1)).val) +
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0)).val)) : Ωˣ) : Ω) =
        (s 0) Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 := by
      show ((Additive.toMul ((Additive.ofMul (galUnitsHom K Ω (s 0) (Yu ^ a1)) : Additive Ωˣ) -
          Additive.ofMul (Yu ^ a01) + Additive.ofMul (Yu ^ a0)) : Ωˣ) : Ω) = _
      simp only [toMul_add, toMul_sub, toMul_ofMul, Units.val_mul, Units.val_div_eq_div_val,
        coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Yu, Units.val_mk0,
        map_pow, div_eq_mul_inv]
    refine Eq.trans hL ?_
    rw [hκ (s 0), mul_pow]
    have hYz : Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 = (algebraMap K Ω (ϖ : K)) ^ cc := by
      rw [← hY, show (Y ^ (N : ℕ)) ^ cc = Y ^ (((N : ℕ) : ℤ) * cc) by rw [zpow_mul, zpow_natCast],
        hrel, zpow_sub₀ hY0, zpow_add₀ hY0, zpow_natCast, zpow_natCast, zpow_natCast]
      ring
    have hζN : ζ ^ (N : ℕ) = 1 := hζ.pow_eq_one
    have hzk : (ζ ^ (κ (s 0)).val) ^ a1 = ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val := by
      rw [← pow_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.div_add_mod ((κ (s 0)).val * a1) (N : ℕ), pow_add, pow_mul, hζN,
        one_pow, one_mul]
    rw [← hzk, ← hYz]
    ring
  have hc0 : cohomologyπ _ 2 c = - cohomologyπ _ 2 w := eq_neg_of_add_eq_zero_left hsum
  rw [hc0, map_neg, hw]
  exact congrArg Neg.neg (brauerInv_galCupClass_urPsi (K := K) (Ω := Ω) N ϖ hϖ)

end HasseMain

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCohCharPf
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resCmpChar0' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : ↥(H0 rho) ≃+ cohomology A 0)
      (Ev : ∀ v, ↥(H0 (rho.comp (lam v))) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 0),
      (∀ v x, Ev v (resH0 rho (lam v)  x) = ptRes φ A v 0 (E x)) ∧
      (∀ (z : ↥(H0 rho)) (x : cocycles A 0),
        (∀ s : Fin 0 → H, cochainOf A (cocycleι A 0 x) s = eM z.1) →
        E z = cohomologyπ A 0 x) ∧
      (∀ v (z : ↥(H0 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 0),
        (∀ s : Fin 0 → Hv v, cochainOf _ (cocycleι _ 0 x) s = eM z.1) →
        Ev v z = cohomologyπ _ 0 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e0, he0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 H R M rho' A eM hM'
  have hEq : H0 rho = H0 rho' := by
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm (θ g)
      change rho (θ.symm (θ g)) m = m at this
      rwa [θ.symm_apply_apply] at this
  let r0 : ↥(H0 rho) ≃ₗ[R] ↥(H0 rho') := LinearEquiv.ofEq _ _ hEq
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev0 hev0 using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have hEqv : ∀ v, H0 (rho.comp (lam v)) = H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom) := by
    intro v
    ext m
    constructor
    · intro hm h
      exact hm _
    · intro hm g
      have := hm ((ev v).symm g)
      change rho (lam v (ev v ((ev v).symm g))) m = m at this
      rwa [MulEquiv.apply_symm_apply] at this
  let rv : ∀ v, ↥(H0 (rho.comp (lam v))) ≃ₗ[R] ↥(H0 ((rho.comp (lam v)).comp (ev v).toMonoidHom)) :=
    fun v => LinearEquiv.ofEq _ _ (hEqv v)
  refine ⟨r0.toAddEquiv.trans e0, fun v => (rv v).toAddEquiv.trans (ev0 v), fun v z => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  have hz' : (z : M) ∈ H0 rho' := hEq ▸ z.2
  obtain ⟨x, hx⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eM z.1) (IsLocallyConstant.const _) (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp rho' A eM hM' 0 fun _ => z.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hz' (s 0), sub_self]
      exact map_zero eM)
  have hE : e0 (r0 z) = cohomologyπ A 0 x := he0 _ x (fun s => congrFun hx s)
  show ev0 v (rv v (resH0 rho (lam v) z)) = ptRes φ A v 0 (e0 (r0 z))
  rw [hE]
  have hP : ptRes φ A v 0 (cohomologyπ A 0 x) =
      cohomologyπ _ 0 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0 x) := by
    unfold ptRes
    exact congrArg (fun f => f.hom x) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
      (continuous_toMonoidHom (φ v)) (𝟙 _) 0)
  rw [hP]
  apply hev0 v
  intro s
  rw [cochainOf_cocycleι_cocyclesMapAlong]
  dsimp only
  rw [hx]
  rfl
  · show e0 (r0 z) = _
    exact he0 _ x (fun s => hx s)
  · show ev0 v (rv v z) = _
    exact hev0 v _ x (fun s => hx s)

theorem resCmpChar1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      (∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x)) ∧
      (∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
        (∀ s : Fin 1 → H, cochainOf A (cocycleι A 1 x) s = eM (z.1 (θ.symm (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x) ∧
      (∀ v (z : ↥(Z1 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 1),
        (∀ s : Fin 1 → Hv v, cochainOf _ (cocycleι _ 1 x) s = eM (z.1 (ev v (s 0)))) →
        Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 1 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)
  · show e1 (r1 (Submodule.Quotient.mk z)) = _
    exact he1b (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z) x (fun s => by rw [hx s]; rfl)
  · show ev1 v (rv v (Submodule.Quotient.mk z)) = _
    exact hev1b v (restrictCocycles1 (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v) z) x (fun s => by rw [hx s]; rfl)

theorem resCmpChar2' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H2 rho ≃+ cohomology A 2)
      (Ev : ∀ v, H2 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 2),
      (∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x)) ∧
      (∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
        (∀ s : Fin 2 → H, cochainOf A (cocycleι A 2 x) s = eM (z.1 (θ.symm (s 0), θ.symm (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x) ∧
      (∀ v (z : ↥(Z2 (rho.comp (lam v)))) (x : cocycles (Rep.res (φ v).toMonoidHom A) 2),
        (∀ s : Fin 2 → Hv v, cochainOf _ (cocycleι _ 2 x) s = eM (z.1 (ev v (s 0), ev v (s 1)))) →
        Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 2 x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e2, he2a, he2b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 H R M rho' A eM hM'
  have bij := resH2_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g)
    (fun h => θ.apply_symm_apply h)
  let r2 : H2 rho ≃ₗ[R] H2 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev2 hev2a hev2b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH2_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g)
    (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H2 (rho.comp (lam v)) ≃ₗ[R] H2 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_, fun z x hx => ?_, fun v z x hx => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he2a (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e2 (r2 (Submodule.Quotient.mk z)) = cohomologyπ A 2 y := he2b _ y hy
    show ev2 v (rv v (resH2 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 2 (e2 (r2 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 2 (cohomologyπ A 2 y) =
        cohomologyπ _ 2 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 2)
    rw [hP]
    apply hev2b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)), θ.symm (φ v (s 1)))) =
      eM (z.1 (lam v (ev v (s 0)), lam v (ev v (s 1))))
    rw [← hev, ← hev]
    exact congrArg (fun t => eM (z.1 t))
      (Prod.ext (θ.symm_apply_apply _) (θ.symm_apply_apply _))
  · show e2 (r2 (Submodule.Quotient.mk z)) = _
    exact he2b (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z) x (fun s => by rw [hx s]; rfl)
  · show ev2 v (rv v (Submodule.Quotient.mk z)) = _
    exact hev2b v (restrictCocycles2 (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v) z) x (fun s => by rw [hx s]; rfl)

end PositivityTheory.Lit1.PTN
end
end

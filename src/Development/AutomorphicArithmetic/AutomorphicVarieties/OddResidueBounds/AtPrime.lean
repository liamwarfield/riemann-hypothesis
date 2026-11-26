module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaDecompSign
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem signTop {O W Q N : Type} [CommRing O] [IsDomain O] [Group W] [Group Q] [IsMulCommutative Q] [Finite Q]
    [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N]
    (π : Representation O W N) (p : W →* Q) (hp : Function.Surjective p) (hker : ∀ g, p g = 1 → ∀ x, π g x = x)
    (h2 : IsUnit (2 : O)) (c : W) (s : ℤˣ) (a : O) (ha : a = ((s : ℤ) : O)) (hc : p c * p c = 1)
    (T : Finset (Q →* Oˣ)) (hT : ∀ ψ, ((ψ (p c) : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) :
    Module.length O (Module.End.eigenspace (π c) a) ≤
      ∑ ψ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) N)
        ((ψ.comp p).comp (⊤ : Subgroup W).subtype)) := by
  subst ha
  let s' : Oˣ := Units.map (Int.castRingHom O).toMonoidHom s
  have hs' : (s' : O) = ((s : ℤ) : O) := rfl
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  exact lenEigSign O (⊤ : Subgroup W) Q N (π.comp (⊤ : Subgroup W).subtype) (p.comp (⊤ : Subgroup W).subtype)
    (fun q => by
      obtain ⟨g, hg⟩ := hp q
      exact ⟨⟨g, trivial⟩, hg⟩)
    (fun g hg x => hker g hg x)
    h2 ⟨c, trivial⟩ s' hc (by rw [← map_mul, Int.units_mul_self, map_one]) T
    (fun ψ hψ => hT ψ (by rw [← hs', ← hψ]; rfl))

theorem UpperTheory.V.Base.shaDecompSign :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAbelianGalois k E] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[k] E))]
      [Fintype ((E ≃ₐ[k] E) →* Oˣ)] (D : LData E Ω l) (e : ℤ), l ≠ 2 → ∀ (c : E ≃ₐ[k] E) (s : ℤˣ), c * c = 1 → ∀ T : Finset ((E ≃ₐ[k] E) →* Oˣ),
      (∀ ψ, ((ψ c : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) →
      Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e c.toRingEquiv) ((s : ℤ) : ℤ_[l])) * eO l O ≤ ∑ ψ ∈ T, Module.length O (shaEig (twist₂ l (chiO k Ω l O ^ (-e))) l (galOf k E Ω) ⊤ ((ψ.comp (AlgEquiv.restrictNormalHom E)).comp (⊤ : Subgroup (G k Ω)).subtype)) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l hl O _ _ _ _ _ _ _ D e hl2 c s hc T hT
  obtain ⟨hsurj, hker, hlift⟩ := galQuot k E Ω
  obtain ⟨σ, rfl⟩ := hsurj c
  have h2 : IsUnit (2 : O) := by
    have := (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  have hχ : chiO k Ω l O ^ (-e) = (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)) := by
    ext g
    simp [chiO]
  have h1 := (shaLenEq k E Ω l D e).2 _ σ (hlift σ) ((s : ℤ) : ℤ_[l])
  have h3 := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-e)) (galOf k E Ω) (shaFam k Ω l)).2 (conjStable_shaFam k Ω l) σ
    ((s : ℤ) : ℤ_[l])
  rw [h1, hχ]
  refine (le_of_eq h3.symm).trans ?_
  exact signTop
    (shaRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)))) l (galOf k E Ω))
    (AlgEquiv.restrictNormalHom E) hsurj
    (fun g hg x => selRep_of_mem _ _ (conjStable_shaFam k Ω l) (hker ▸ MonoidHom.mem_ker.2 hg) x)
    h2 σ s _ (map_intCast (algebraMap ℤ_[l] O) _) hc T hT
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ChiFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.chiFacts :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), Function.Surjective ρ → ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)), Function.Injective (fun ψ : (E ≃ₐ[ℚ] E) →* Oˣ => chiOf ρ ψ) ∧ ∀ (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) (k : ℕ), (chiOf ρ ψ (-1) = (-1) ^ k → chiOf ρ ψ ∈ charSet (PadicAlgCl l) (parE ρ k)) ∧ ∃ a : O, (a : PadicAlgCl l) = alN k (chiOf ρ ψ) := by
  intro E _ _ N _ ρ hρ l _ O
  refine ⟨fun ψ ψ' h => ?_, fun ψ k => ⟨fun hk => ?_, ?_⟩⟩
  · refine MonoidHom.ext fun g => ?_
    obtain ⟨b, rfl⟩ := hρ g
    have hb := congrArg (fun χ : DirichletCharacter (PadicAlgCl l) N => χ (b : ZMod N)) h
    simp only [chiOf_unit] at hb
    exact Units.ext (Subtype.ext hb)
  · simp only [charSet, parE, Set.mem_setOf_eq, Set.mem_inter_iff]
    refine ⟨?_, (b_parity k _).1.2 hk⟩
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, chiOf_unit, hb]
    simp
  · have h := (b_primmem k (chiOf ρ ψ)).2.1 O.toSubring (fun u => by
      rw [chiOf_unit]
      exact (ψ (ρ u) : O).2)
    exact ⟨⟨_, h⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.PsiReal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.psiReal :
    PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω] [IsAlgClosure E Ω] [IsAlgClosure ℚ Ω] [IsAbelianGalois ℚ E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (e : ℕ), 1 ≤ e → ∀ ψ : (E ≃ₐ[ℚ] E) →* Oˣ, chiOf ρ ψ (-1) = (-1) ^ (e + 1) → psiLen (l := l) Ω e ψ ≠ ⊤ ∧ ((psiLen (l := l) Ω e ψ).toNat : ℝ) * Real.log l ≤ ((eO l O).toNat : ℝ) * -Real.log ‖alN (e + 1) (chiOf ρ ψ)‖ := by
  intro hPB E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hψ
  obtain ⟨hsurj, -⟩ := actFacts E Ω N ρ hρ
  obtain ⟨-, hF⟩ := chiFacts E N ρ hsurj l O
  obtain ⟨-, a, ha⟩ := hF ψ (e + 1)
  have hle := hPB E Ω N ρ hρ l hl2 hlE O e he ψ hψ a ha
  have hB := (b_nzany (chiOf ρ ψ) (e + 1) (by omega) hψ).1
  have hane : (a : PadicAlgCl l) ≠ 0 := by
    rw [ha]
    simp only [alN]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (den_pos (Nat.pos_of_ne_zero (NeZero.ne N)) _).ne') hB
  have ha0 : a ≠ 0 := fun h => hane (by simp [h])
  have hval : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha0
  refine ⟨ne_top_of_le_ne_top hval hle, ?_⟩
  have hn := normO l O a ha0
  have hpos : 0 < ‖(a : PadicAlgCl l)‖ := norm_pos_iff.mpr hane
  have hlog := congrArg Real.log hn
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at hlog
  rw [← ha]
  have hmono : ((psiLen (l := l) Ω e ψ).toNat : ℝ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℝ) := by
    exact_mod_cast ENat.toNat_le_toNat hle hval
  have hl : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  nlinarith [mul_le_mul_of_nonneg_right hmono hl]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem divE {ι : Type} (T : Finset ι) (m r : ℕ∞) (f : ι → ℕ∞) (g : ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hr0 : r ≠ 0) (hr : r ≠ ⊤) (h : m * r ≤ ∑ i ∈ T, f i)
    (hf : ∀ i ∈ T, f i ≠ ⊤ ∧ ((f i).toNat : ℝ) * L ≤ (r.toNat : ℝ) * g i) :
    m ≠ ⊤ ∧ (m.toNat : ℝ) * L ≤ ∑ i ∈ T, g i := by
  have hfe : ∑ i ∈ T, f i = ((∑ i ∈ T, (f i).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i hi => (ENat.coe_toNat (hf i hi).1).symm)
  lift r to ℕ using hr
  have hm : m ≠ ⊤ := by
    rintro rfl
    rw [hfe, ENat.top_mul hr0] at h
    exact ENat.coe_ne_top _ (top_le_iff.1 h)
  lift m to ℕ using hm
  refine ⟨ENat.coe_ne_top _, ?_⟩
  rw [hfe, ← Nat.cast_mul, Nat.cast_le] at h
  simp only [ENat.toNat_coe] at hf ⊢
  have hrpos : (0 : ℝ) < r := by
    have : r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Nat.pos_of_ne_zero this
  have h1 : (m : ℝ) * r * L ≤ ∑ i ∈ T, ((f i).toNat : ℝ) * L := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hL
    exact_mod_cast h
  have h2 : ∑ i ∈ T, ((f i).toNat : ℝ) * L ≤ ∑ i ∈ T, (r : ℝ) * g i :=
    Finset.sum_le_sum (fun i hi => (hf i hi).2)
  rw [← Finset.mul_sum] at h2
  have h3 : (r : ℝ) * ((m : ℝ) * L) ≤ (r : ℝ) * ∑ i ∈ T, g i :=
    calc (r : ℝ) * ((m : ℝ) * L) = (m : ℝ) * r * L := by ring
      _ ≤ _ := h1.trans h2
  exact le_of_mul_le_mul_left h3 hrpos

private theorem keyO (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ E Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure E Ω] [IsAbelianGalois ℚ E] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E))] (D : LData E Ω l) (e : ℕ) (hl2 : l ≠ 2) (c : E ≃ₐ[ℚ] E)
    (hc : c * c = 1) (hcE : c.toRingEquiv = cE E) (T : Finset ((E ≃ₐ[ℚ] E) →* Oˣ))
    (hT : ∀ ψ, ((ψ c : Oˣ) : O) = (-1) ^ (e + 1) → ψ ∈ T) :
    minusLen D e * eO l O ≤ ∑ ψ ∈ T, psiLen (l := l) Ω e ψ := by
  haveI : Fintype ((E ≃ₐ[ℚ] E) →* Oˣ) := Fintype.ofFinite _
  have key := shaDecompSign ℚ E Ω l O D (e : ℤ) hl2 c ((-1) ^ (e + 1)) hc T (fun ψ h => hT ψ (by simpa using h))
  have hsgn : ((((-1) ^ (e + 1) : ℤˣ) : ℤ) : ℤ_[l]) = (-1) ^ (e + 1) := by simp
  rw [hcE, hsgn] at key
  exact key

theorem UpperTheory.V.Odd.atPrime :
    PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ e : ℕ, 1 ≤ e → minusLen D e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N), (T : Set _) ⊆ charSet (PadicAlgCl l) (parE ρ (e + 1)) ∧ ((minusLen D e).toNat : ℝ) * Real.log l ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖ := by
  classical
  intro hPB E Ω _ _ _ _ _ _ N _ ρ hρ l _ D hl2 hld e he
  obtain ⟨hsurj, hab, -, -, -⟩ := UpperTheory.V.Odd.actFacts E Ω N ρ hρ
  haveI := hab
  obtain ⟨hcE, -⟩ := UpperTheory.V.Odd.actConj E Ω N ρ hρ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ E Ω
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨O, hO1, hO2, hO3⟩ := UpperTheory.V.Base.existsO l (Monoid.exponent (E ≃ₐ[ℚ] E))
  haveI := hO1
  haveI := hO2
  haveI := hO3
  haveI := Fintype.ofFinite ((E ≃ₐ[ℚ] E) →* Oˣ)
  obtain ⟨-, -, -, -, -, heO0, heOle, -, -⟩ := UpperTheory.V.Base.dvrFacts l O
  have hc : ρ (-1) * ρ (-1) = 1 := by
    rw [← map_mul]
    simp
  let T : Finset ((E ≃ₐ[ℚ] E) →* Oˣ) :=
    Finset.univ.filter (fun ψ => ((ψ (ρ (-1)) : Oˣ) : O) = (-1) ^ (e + 1))
  have hkey := keyO E Ω l O D e hl2 (ρ (-1)) hc hcE T
    (fun ψ hψ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hψ⟩)
  have hpar : ∀ ψ ∈ T, chiOf ρ ψ (-1) = (-1) ^ (e + 1) := by
    intro ψ hψ
    have hψ' := (Finset.mem_filter.1 hψ).2
    have h1 := chiOf_unit ρ ψ (-1)
    rw [Units.val_neg, Units.val_one] at h1
    rw [h1, hψ']
    simp
  have hfin : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) heOle
  have hL : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  obtain ⟨hm, hle⟩ := divE T (minusLen D e) (eO l O) (fun ψ => psiLen (l := l) Ω e ψ)
    (fun ψ => -Real.log ‖alN (e + 1) (chiOf ρ ψ)‖) (Real.log l) hL heO0 hfin hkey
    (fun ψ hψ => UpperTheory.V.Odd.psiReal hPB E Ω N ρ hρ l hl2 hld O e he ψ (hpar ψ hψ))
  refine ⟨hm, T.image (fun ψ => chiOf ρ ψ), ?_, ?_⟩
  · rw [Finset.coe_image]
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ((UpperTheory.V.Odd.chiFacts E N ρ hsurj l O).2 ψ (e + 1)).1 (hpar ψ hψ)
  · rw [Finset.sum_image (fun x _ y _ h => (UpperTheory.V.Odd.chiFacts E N ρ hsurj l O).1 h)]
    exact hle

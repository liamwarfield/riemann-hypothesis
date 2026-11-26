module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AbsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagAb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterKerOpenTrivialRationalArchimedean
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_root (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (hm : 0 < m)
    (d : Ideles E) (hd : pFin E (d : Ad E) = 1) : ∃ y : Ideles E, y ^ m = d := by
  have h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h
  let Y : Ad E := ((y : InfiniteAdeleRing E), (1 : Af E))
  have hY : Y ^ m = (d : Ad E) := Prod.ext (funext hy) ((one_pow m).trans hd.symm)
  have hu : IsUnit Y := (isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩

theorem UpperTheory.detCharacter_ker_open_trivial_rational_archimedean :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E) (m : ℕ), 0 < m → ν.OrderDvd m → IsOpen (((chiDet n ν).comp (UA E n).subtype).ker : Set (UA E n)) ∧ (∀ g ∈ ratU E n, chiDet n ν (g : UA E n) = 1) ∧ ∀ g ∈ infU E n, chiDet n ν (g : UA E n) = 1 := by
  intro E _ _ _ n ν m hm h
  have h1 : ∀ x, ν.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  refine ⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩
  · exact ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  · intro g hg
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
    rw [← hγ, chiDet_ratGL]
  · intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1 := hg
    obtain ⟨y, hy⟩ := exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by
      rw [← GlobalTheory.CuspRep.det_map, hg']; simp)
    change ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1
    rw [← hy, map_pow, h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterOfAlgebraicHecke
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_rank_one_rep {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
  ext g
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

private theorem tw_eq {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l)) (μ : Γ →* (Qbar l)ˣ) :
    Af.tw R μ = Formalism.MainNotions.SumRepresentations.At.twGL R (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
  rw [det_rank_one_rep]
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

private theorem tw_comp {Γ Γ' : Type} [Group Γ] [Group Γ'] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l))
    (μ : Γ →* (Qbar l)ˣ) (f : Γ' →* Γ) :
    (Af.tw R μ).comp f = Formalism.MainNotions.SumRepresentations.At.twGL (R.comp f) (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp f)) := by
  rw [tw_eq]; rfl

private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this

theorem UpperTheory.galois_character_of_algebraic_hecke :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R → (∃ HT, Af.HasHT R HT) → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsAlgPos κ m → Continuous μ → IsLAdicOf art ι κ m μ → (∃ HT, Af.HasHT (Af.tw R μ) HT) ∧ ∀ (w : Plc K) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))), Af.LocGlob ι R w τ → Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Af.LocGlob ι (Af.tw R μ) w τ' := by
  intro P K Ω _ _ _ _ _ _ l _ ι n R hR hHT art κ m μ hart hκ hμ hL
  obtain ⟨HT, hHT⟩ := hHT
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have H1 : Af.HasHT (Af.tw R μ) fun τ => (HT τ).map (· + -m (ι.toRingHom.comp τ)) := by
    intro w A h O _ _ _ Bw hj
    obtain ⟨d1, j1⟩ := hHT w A h O Bw hj
    obtain ⟨d2, -, -, j2⟩ :=
      GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj
    have t := GlobalTheory.TwistAbove.twist_above l _ _ ⟨T⟩ K Ω _ O Bw n (R.comp (Dec (F := K) A).subtype)
      ((Af.tw R μ).comp (Dec (F := K) A).subtype) (μ.comp (Dec (F := K) A).subtype) fun g => Af.tw_val R μ g.1
    exact ⟨t.1 d1 d2, fun τ L' τ' hτ => t.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ)⟩
  refine ⟨⟨_, H1⟩, fun w τ τ' hτ he A h rc hrc => ?_⟩
  obtain ⟨h1, h2⟩ := hτ A h rc hrc
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have e : rc (algNorm τ') = (rc (algNorm τ)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [rec_algNorm hrc, rec_algNorm hrc, GlobalTheory.NuShift.lpChar_lpTw]
    obtain ⟨a, ha, ε, -, HL⟩ := hrc
    rw [← HL.twist, GlobalTheory.LocGL.IrrGL.tw_of]
    exact congrArg (fun x => (rc x).lpTw _) (IrrGL.of_eq_of.2 he)
  rw [e]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hc.1]
  have hcR := Units.continuous_val.comp hR
  have hct : Continuous fun g => ((Af.tw R μ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    simp only [Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul hcR
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩
  · have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
      fun g => rfl
    have h3 := isWDOf_wdOf (h := h) (r := Af.tw R μ) hw ι hct
    have h4 := wdOf_twGL_det K Ω A w h l hw ι n R _ hcR (continuous_rank_one_rep hμ)
    rw [← tw_eq, (h1 hw).wdOf_eq hw,
      wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (κ.loc w).comp a) fun _ => ha.smooth hc.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h4
    rw [h4] at h3
    exact h3
  · obtain ⟨p1, w1⟩ := h2 O Bw hj
    have p3 := P.aut.berger.isPstAt T Bw _ (hct.comp continuous_subtype_val) (H1 w A h O Bw hj).1
    have c2 := (continuous_rank_one_rep hμ).comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A))
    have p2 := P.aut.berger.isPstAt T Bw ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype) c2
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj).1
    refine ⟨p3, ?_⟩
    have htw : (Af.tw R μ).comp (Dec (F := K) A).subtype =
        Formalism.MainNotions.SumRepresentations.At.twGL (R.comp (Dec (F := K) A).subtype)
          (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)) := by
      exact tw_comp R μ _
    rw [htw] at p3 ⊢
    rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι K Ω A w h O Bw hj n _ _ (hcR.comp continuous_subtype_val) c2 p1 p2 p3,
      P.aut.chW K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj _ hc a ha]
    refine ((UpperTheory.V.Lev.ssCalc K Ω A w h).2.2 _ _ _ ?_).2 w1
    rw [← HL.one _ hc.1]
    exact HL.dim _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicRepTwistByCharacter
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulCh {Γ : Type} [Group Γ] (χ : Γ →* ℂˣ) : (Γ → ℂ) ≃ₗ[ℂ] (Γ → ℂ) where
  toFun φ g := (χ g : ℂ) * φ g
  invFun φ g := ((χ g)⁻¹ : ℂˣ) * φ g
  map_add' φ ψ := by ext g; simp [mul_add]
  map_smul' c φ := by ext g; simp [mul_left_comm]
  left_inv φ := by ext g; simp
  right_inv φ := by ext g; simp

private theorem cont_ch {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (χ : Γ →* ℂˣ)
    (h : IsOpen (χ.ker : Set Γ)) : Continuous fun g => (χ g : ℂ) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one χ ?_)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h.mem_nhds χ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.1 hg).symm

private theorem irr_tw {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    ρ.IsIrreducible ↔ (twRep ρ η).IsIrreducible := by
  rw [isIrreducible_iff, isIrreducible_iff]
  refine and_congr_right fun _ => forall_congr' fun W => imp_congr_left ?_
  refine forall_congr' fun g => forall_congr' fun v => forall_congr' fun _ => ?_
  exact (W.smul_mem_iff (Units.ne_zero (η g))).symm

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : UA E n →* ℂˣ)

private theorem RU_mulCh (x : UA E n) (φ : UA E n → ℂ) :
    RU E n x (mulCh χ φ) = (χ x : ℂ) • mulCh χ (RU E n x φ) := by
  ext g
  change (χ (g * x) : ℂ) * φ (g * x) = (χ x : ℂ) * ((χ g : ℂ) * φ (g * x))
  rw [map_mul, Units.val_mul]; ring

private theorem form_mulCh (ho : IsOpen (χ.ker : Set (UA E n))) (hr : ∀ g ∈ ratU E n, χ g = 1) {φ : UA E n → ℂ}
    (h : IsAutFormU φ) : IsAutFormU (mulCh χ φ) := by
  refine ⟨(cont_ch χ ho).mul h.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change (χ (γ * g) : ℂ) * φ (γ * g) = (χ g : ℂ) * φ g
    rw [map_mul, hr γ hγ, one_mul, h.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E n).comp (finU (E := E) (n := n)).subtype) (mulCh χ φ) ?_
    have h2 : IsOpen ((Subtype.val : finU (E := E) (n := n) → UA E n) ⁻¹' (χ.ker : Set (UA E n))) := ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset ((h.level.inter h2).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E n 1 φ = φ
      simp
    · exact χ.ker.one_mem
    · have h1 : RU E n k φ = φ := hk.1
      have h3 : χ k = 1 := hk.2
      change RU E n k (mulCh χ φ) = mulCh χ φ
      rw [RU_mulCh, h1, h3]; simp
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (mulCh χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k (mulCh χ φ) ∈ _
    rw [RU_mulCh]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))
end

theorem UpperTheory.exists_automorphicRep_twist_by_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (χ : UA E n →* ℂˣ), IsOpen (χ.ker : Set (UA E n)) → (∀ g ∈ ratU E n, χ g = 1) → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∃ σ' : Submodule ℂ (UA E n → ℂ), IsAutRepU σ' ∧ (∀ w : Plc E, (∀ g ∈ locU n w, cLoc w g ∈ GlobalTheory.LFun.KGL w (n := n) → χ g = 1) → IsUnramU σ w → IsUnramU σ' w) ∧ ∀ (Gv : Subgroup (UA E n)) (H M : Type) [Group H] [AddCommGroup M] [Module ℂ M] (p : Gv →* H) (ρ : Representation ℂ H M) (η : H →* ℂˣ), (∀ x : Gv, χ x = η (p x)) → (IsCompAlong σ Gv p ρ ↔ IsCompAlong σ' Gv p (twRep ρ η)) := by
  intro E _ _ _ n χ ho hr σ hσ
  refine ⟨σ.comap (mulCh χ).symm.toLinearMap, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun e => ?_, fun W hW hs => ?_⟩,
    fun w hw ⟨φ, hφ, h0, hf⟩ => ?_, fun Gv H M _ _ _ p ρ η hη => and_congr (irr_tw ρ η) ⟨?_, ?_⟩⟩
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    exact form_mulCh χ ho hr (hσ.aut ψ (by simpa using hφ))
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    rw [RU_mulCh]
    refine Submodule.smul_mem _ _ ?_
    simpa using hσ.stable x ψ (by simpa using hφ)
  · refine hσ.ne_bot (eq_bot_iff.2 fun φ hφ => ?_)
    have : mulCh χ φ ∈ σ.comap (mulCh χ).symm.toLinearMap := by simpa using hφ
    rw [e] at this
    simpa using this
  · have := hσ.irred (W.comap (mulCh χ).toLinearMap) (fun φ hφ => by simpa using hW hφ) fun x φ hφ => by
      have := hs x _ hφ
      change RU E n x (mulCh χ φ) ∈ W at this
      rw [RU_mulCh] at this
      exact (W.smul_mem_iff (Units.ne_zero (χ x))).1 this
    refine this.imp (fun e => eq_bot_iff.2 fun φ hφ => ?_) fun e => le_antisymm hW fun φ hφ => ?_
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ W.comap (mulCh χ).toLinearMap := hφ
      rw [e] at this
      simpa using this
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ σ := by simpa using hφ
      rw [← e] at this
      exact this
  · refine ⟨mulCh χ φ, by simpa using hφ, by simpa using h0, fun x hx hk => ?_⟩
    rw [RU_mulCh, hf x hx hk, hw x hx hk]; simp
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => by simpa using h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · change mulCh χ (f ((η (p x) : ℂ) • ρ (p x) v)) = RU E n x (mulCh χ (f v))
      rw [RU_mulCh, map_smul, map_smul, h2, hη]
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).symm.toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · apply (mulCh χ).injective
      apply smul_right_injective _ (Units.ne_zero (χ x))
      have := h2 x v
      rw [twRep_apply, map_smul, ← hη] at this
      change (χ x : ℂ) • mulCh χ ((mulCh χ).symm (f (ρ (p x) v))) = (χ x : ℂ) • mulCh χ (RU E n x ((mulCh χ).symm (f v)))
      rw [← RU_mulCh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, this]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaCharEqSelfOfConjugateDual
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conjSrc_eq {E : Type} [Field E] [NumberField E] (τ : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc τ w = preplace τ w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : Af.IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

theorem UpperTheory.thetaChar_eq_self_of_conjugate_dual :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (κ : HChar E) (m : ℕ), 0 < m → κ.OrderDvd m → ∀ β : G E Ω →* (Qbar l)ˣ, Continuous β → IsLAdicOf art ι κ 0 β → ∀ c : G (maximalRealSubfield E) Ω, Af.IsConjEl c → (∀ s s' : G E Ω, s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ → β s' = (β s)⁻¹) → GlobalTheory.ThetaPull.thetaChar κ = κ := by
  intro E Ω _ _ _ _ _ _ l _ ι art ha κ m _ _ β _ hL c hc hβ
  have hLi := isLift_conj hc
  have hval : ∀ v, κ.UnrAt v → κ.UnrAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) →
      κ.val (conjSrc (IsCMField.complexConj E).toRingEquiv v) = (κ.val v)⁻¹ := by
    intro v hv hv'
    rw [conjSrc_eq] at hv' ⊢
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
    have e1 := hL.frob_unr ha (Or.inr rfl) hv hA hσ
    have e2 := hL.frob_unr ha (Or.inr rfl) hv' (isPlaceOver_preplace hLi hAA hA) (σ := conjGal hLi σ)
      (by rw [normV_preplace]; exact isFrob_conjGal hLi hAA hσ)
    rw [hβ σ (conjGal hLi σ) (AlgEquiv.ext fun _ => rfl), Units.val_inv_eq_inv_val, e1, inv_inj, ← map_inv₀] at e2
    exact Units.ext (by rw [Units.val_inv_eq_inv_val]; exact (ι.symm.injective e2).symm)
  have hu := GlobalTheory.GalChar.unr_ae κ
  have hu' := (Function.LeftInverse.injective (GlobalTheory.ThetaPull.conjSrc_conjSrc (E := E))).tendsto_cofinite.eventually hu
  have hS := Filter.eventually_cofinite.1 (hu.and hu')
  have h : (GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ ((GlobalTheory.ThetaPull.thetaChar κ).2.1.mul κ.2.1.inv) (fun k => ?_) hS.toFinset
      fun v hv => ?_
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, κ.2.2, (GlobalTheory.ThetaPull.thetaChar κ).2.2, inv_one, one_mul]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      obtain ⟨v, rfl⟩ : ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := ⟨_, GlobalTheory.ThetaPull.conjSrc_conjSrc v⟩
      rw [GlobalTheory.ThetaPull.conjSrc_conjSrc] at hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (((GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹).comp (localIdele E _)) fun y hy => ?_
      have hy' : IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom y) := ((conjLoc_spec _ v).2.2 y.val).trans hy
      have h1 : κ.1 (localIdele E _ y) = κ.val _ := κ.val_eq hv.1 y hy
      have h2 : κ.1 (localIdele E v _) = κ.val v := κ.val_eq hv.2 _ hy'
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ThetaPull.thetaChar_apply,
        GlobalTheory.ThetaPull.conjAd_localIdele, h1, h2, hval v hv.2 hv.1, mul_inv_cancel]
  exact Subtype.ext (mul_inv_eq_one.1 h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterEqLocalDetSplitNonsplit
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_finGL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (k : GL (Fin n) (Af E))
    (hk : ∀ u, cLoc u g = Matrix.GeneralLinearGroup.map (pLoc E u) k) : (g : GA E n) = finGL E n k := by
  have hinf : cInf g = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1
  refine ga_ext (hinf.trans (pInf_finGL k).symm) ?_
  rw [pFin_finGL]
  refine Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)
  exact congrArg Units.val (hk u)

private theorem cLoc_off {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w u : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (hu : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    cLoc u g = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)

theorem UpperTheory.detCharacter_eq_localDet_split_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E), GlobalTheory.ThetaPull.thetaChar ν = ν → ∀ (w : Plc E), ∀ g ∈ locU n w, (IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n (ν * ν) w (cLoc w g)) ∧ (¬ IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n ν w (cLoc w g)) := by
  intro E _ _ _ n ν hν w g hg
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨hne, hun, hover⟩ := GlobalTheory.SplitPts.over_split hw
    set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'
    have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g)) := by
      refine eq_finGL hg _ fun u => ?_
      rw [map_mul]
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]
      · by_cases h2 : u = w'
        · rw [h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]
        · rw [pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]
          exact cLoc_off hg fun h => (hover u h).elim h1 h2
    have hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) =
        (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      have h := congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      refine Eq.trans ?_ h
      exact congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)
    have h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g) := by
      change ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) =
        ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))
      have h3 := GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))
      rw [hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv] at h3
      exact h3
    rw [e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]
    rfl
  · have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g)) := by
      refine eq_finGL hg _ fun u => ?_
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL]
      · rw [pLoc_locGL_of_ne h1]
        exact cLoc_off hg fun h => hw ⟨u, h1, h⟩
    rw [e, CuspSub.chiDet_locGL]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Lev

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω}

end Lev


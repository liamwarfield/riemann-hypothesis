module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst

namespace GlobalTheory.TwistAbove

def twGL {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K) :
    Γ →* GL (Fin a) K where
  toFun g := ⟨((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    (((χ g)⁻¹ : Kˣ) : K) • (((r g)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by rw [smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [smul_mul_smul_comm, Units.inv_mul, Units.inv_mul, one_smul]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    change ((χ (g * h) : Kˣ) : K) • ((r (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *
      (((χ h : Kˣ) : K) • ((r h : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))
    rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul, Units.val_mul])

@[simp] theorem twGL_val {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (g : Γ) : ((twGL χ r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      ((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

abbrev chr {L : FinExt l} (m : ↥Gw →* GL (Fin 1) ↥L.1) : ↥Gw →* (↥L.1)ˣ :=
  Matrix.GeneralLinearGroup.det.comp m

theorem isModel_twGL {L : FinExt l} {r r' : ↥Gw →* GL (Fin a) (Om l)} {μ : ↥Gw →* (Om l)ˣ}
    (hr' : ∀ g, ((r' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ((μ g : (Om l)ˣ) : Om l) • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw (rk1 μ) L m) :
    IsModel Bw r' L (twGL (chr m) r₁) := by
  refine ⟨h₁.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) h₁.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) h₂.2
  simp only [mapRep, rk1] at e1 e2 ⊢
  simp at e1 e2 ⊢
  rw [hr']
  simp [← e1, ← e2]

section Common

variable {L : FinExt l} (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (m : ↥Gw →* GL (Fin 1) ↥L.1)

theorem repE_twGL (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (twGL (chr m) r₁) g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L r₁ g x := by
  change Matrix.toLin' ((twGL (chr m) r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem repE_rank_one (g : ↥(GK Bw.Kw)) (x : Fin 1 → ↥L.1) :
    Bw.repE L m g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • x := by
  funext i
  fin_cases i
  simp [LocBridge.repE, Matrix.mulVec, dotProduct, Matrix.det_unique]

theorem isDR_iff (P : LocPrime l) {n : ℕ} (s : ↥Gw →* GL (Fin n) ↥L.1) :
    IsDR (P.PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE P L s := by
  rw [IsDR, LocBridge.IsdRE, Module.finrank_fin_fun]

theorem twist_common {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    (Bw.IsdRE P L r₁ → Bw.IsdRE P L m → Bw.IsdRE P L (twGL (chr m) r₁)) ∧
    (Bw.IsCrysE P L r₁ → Bw.IsCrysE P L m → Bw.IsCrysE P L (twGL (chr m) r₁)) ∧
    (Bw.IsPotCrysE P L r₁ → Bw.IsPotCrysE P L m → Bw.IsPotCrysE P L (twGL (chr m) r₁)) ∧
    ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (b : ℤ), Bw.IsdRE P L m →
      (∀ n, Bw.multE P L m τ' n = if n = b then 1 else 0) →
      ∀ n, Bw.multE P L (twGL (chr m) r₁) τ' (n + b) = Bw.multE P L r₁ τ' n := by
  have hν := repE_rank_one Bw m
  have hρ := repE_twGL Bw r₁ m
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [← isDR_iff] at h1 h2 ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ h2).1 h1
  · exact (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T Bw.Kw L (Fin a → ↥L.1)
      _ _ _ _ hν hρ h2).1 h1
  · rintro ⟨K₁, k₁, c₁⟩ ⟨K₂, k₂, c₂⟩
    have l₁ : K₁.1 ≤ (supExt K₁ K₂).1 := le_sup_left
    have l₂ : K₂.1 ≤ (supExt K₁ K₂).1 := le_sup_right
    have k₃ : Bw.Kw.1 ≤ (supExt K₁ K₂).1 := k₁.trans l₁
    have d₁ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₁ _ T c₁
    have d₂ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₂ _ T c₂
    have e₁ : ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₁))).comp (Subgroup.inclusion (GK_le l₁)) =
        (Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    have e₂ : ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₂))).comp (Subgroup.inclusion (GK_le l₂)) =
        (Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    rw [e₁] at d₁
    rw [e₂] at d₂
    exact ⟨supExt K₁ K₂, k₃, (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T
      (supExt K₁ K₂) L (Fin a → ↥L.1) ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃))) _
      ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃))) _ (fun g x => hν _ x) (fun g x => hρ _ x) d₂).1 d₁⟩
  · intro τ' b hm hmult n
    exact GlobalTheory.TwistJump.multV_twist_char l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ
      ((isDR_iff Bw P m).2 hm) τ' b hmult n

end Common

theorem twist_above : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ), ∀ (r r' : ↥Gw →* GL (Fin a) (Loc.Om l)) (μ : ↥Gw →* (Loc.Om l)ˣ), (∀ g, ((r' g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) = ((μ g : (Loc.Om l)ˣ) : Loc.Om l) • ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → (IsdRAt P Bw r → IsdRAt P Bw (rk1 μ) → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 μ) → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw (rk1 μ) → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Loc.Om l) (J : Multiset ℤ) (c : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 μ) τ {c} → IsJumpsAt P Bw r' τ (J.map (· + c)) := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r r' μ hr'
  obtain ⟨T⟩ := hT
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun τ J c h1 h2 => ?_⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.1 ((local_ext P Bw l₁ r₁).1.2 d₁) ((local_ext P Bw l₂ r₂).1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.2.1 ((local_ext P Bw l₁ r₁).2.2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁, τ₁, i₁, c₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂, τ₂, i₂, c₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have j₁ : IsInduced Bw τ ((IntermediateField.inclusion l₁).comp τ₁) := fun x => i₁ x
    have j₂ : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ₂) := fun x => i₂ x
    have eτ := IsInduced.unique j₁ j₂
    have hd₂ := (local_ext P Bw l₂ r₂).2.1.2 d₂
    have hc := twist_common Bw (mapRep (IntermediateField.inclusion l₁).toRingHom r₁)
      (mapRep (IntermediateField.inclusion l₂).toRingHom r₂) T
    have hm : ∀ n, Bw.multE P (supExt L₁ L₂) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
        ((IntermediateField.inclusion l₁).comp τ₁) n = if n = c then 1 else 0 := by
      intro n
      rw [eτ, (local_ext P Bw l₂ r₂).2.2.2 τ₂ n, ← c₂ n, Multiset.count_singleton]
      split_ifs <;> simp
    refine ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      hc.1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) hd₂, _, j₁, fun n => ?_⟩
    have e1 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) J (add_left_injective c) (n - c)
    simp only [sub_add_cancel] at e1
    have e2 := hc.2.2.2 _ c hd₂ hm (n - c)
    rw [sub_add_cancel] at e2
    rw [e1, e2, (local_ext P Bw l₁ r₁).2.2.2 τ₁ (n - c), c₁]

end GlobalTheory.TwistAbove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ChiOneNoPt

open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation

abbrev sOne (D : D7) : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = Polynomial.X - Polynomial.C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

theorem integral (D : D7) (hB : BlockCharParam D) (i : D.nd.Loc) :
    ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) τ,
      ∃ k : ℤ, z + ((sOne D : ℝ) : ℂ) = (k : ℂ) := by
  intro τ z hz
  obtain ⟨ρ, b, rfl⟩ := exists_embOver D τ
  obtain ⟨a, ha⟩ := firstJump_int D i ρ b
  have hm : z + (blockExp D 1 : ℂ) ∈
      (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ b)).map (· + (blockExp D 1 : ℂ)) :=
    Multiset.mem_map_of_mem (· + (blockExp D 1 : ℂ)) hz
  rw [inf_block D hB i 1 ρ b, Multiset.mem_singleton] at hm
  have hs : blockExp D 1 = sOne D := by simp [blockExp, sOne]
  refine ⟨-a, ?_⟩
  rw [← hs, hm, ha]
  push_cast
  ring

theorem eq_chi (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (w₀ : HeightOneSpectrum (𝓞 D.host.E))
    (hw₀ : w₀ ∈ placesOver D.host.E (D.nd.l i)) (ρ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)))
    (hc : Continuous fun g =>
      ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))))
    (haway : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (sOne D)) :
    ρ = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
  have hl : (placesOver D.host.E (D.nd.l i)).Finite := by
    have h0 : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.nd.lPrime i).out.ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let Sg : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i)
  have hSg : Sg.Finite := (hl.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hd := h5.2.2.1 Sg hSg
  have key : (fun g => ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
      fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    refine Continuous.ext_on (dense_iff_closure_eq.2 hd)
      ((continuous_apply 0).comp ((continuous_apply 0).comp hc))
      ((continuous_iotaOQ D i w₀ hw₀).comp (D.nd.chi_cont i 1)) ?_
    rintro σ ⟨w, hwS, hsp, B, hB, hσ⟩
    simp only [Sg, Set.mem_union, Finset.mem_coe, not_or] at hwS
    have hso : SplitOut D.nd i w := ⟨hsp, hwS.1.1, hwS.1.2, hwS.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i w hso
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [haway w hwS.1.1]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hwS.1.1 hc hun B σ hB hσ
    rw [haway w hwS.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    exact (D.naut.iotaQC i).injective (Polynomial.C_inj.1 (sub_right_injective e))
  ext g a b
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : b = 0 := Subsingleton.elim _ _
  refine (congrFun key g).trans ?_
  rw [← chiGL_apply D i 1 g 0 0]
  rfl

theorem isConstituent_chiGL (D : D7) (i : D.nd.Loc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (D.nd.chi i 1) ((Units.coeHom _).comp (chiGL D i 1)) := by
  refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), fun g => ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, mapM, chiGL]

end GlobalTheory.ChiOneNoPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheorem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheorem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedRegular

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem regular_onto (h : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) :
    (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
    (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
    ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  refine ⟨fun K b hb hg => ?_, fun u => ?_, fun K w => ?_⟩
  · have hu : IsUnit (T.eB b) := by
      refine h.regular C K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hgK => ?_
      obtain ⟨x, hx⟩ := hg g hgK
      refine ⟨x, ?_⟩
      rw [← T.actB, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
      rfl
    simpa using hu.map T.eB.symm
  · obtain ⟨x, hx⟩ := GlobalTheory.Published.FontaineBcris.oneSubPhiOnto_of_filZero (h.ontoFilZero C) (T.eB u)
    refine ⟨T.eB.symm x, T.eB.injective ?_⟩
    rw [map_sub, T.frob, RingEquiv.apply_symm_apply, hx]
  · obtain ⟨x, hx, hF⟩ := h.fundOnto C (T.eD w)
    refine ⟨T.eB.symm x, T.eB.injective ?_, ?_⟩
    · rw [T.frob, RingEquiv.apply_symm_apply, hx]
    · rw [T.fil, map_sub, hC.ι, RingEquiv.apply_symm_apply]
      exact hF

end GlobalTheory.MemLoc.TiedRegular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheoremStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.TiedRegular.regular_onto | exact GlobalTheory.MemLoc.TiedRegular.regular_onto | (intros; apply GlobalTheory.MemLoc.TiedRegular.regular_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.MemLoc

theorem tied_regular_and_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 →
        (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
      (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
      ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 :=
  GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem GlobalTheory.T.fontaineBcrisBasicTheorems_proof

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFilStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRings_regular_phi_surjective_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.tied_regular_and_onto | exact GlobalTheory.MemLoc.tied_regular_and_onto | (intros; apply GlobalTheory.MemLoc.tied_regular_and_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
noncomputable section

namespace GlobalTheory.TwistRepCrys

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fildR_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) := by
  rw [GlobalTheory.HTW.FildR_eq_comap PD ρ ρ' e.toLinearMap e.injective he τ a]
  exact (LinearEquiv.ofSubmodule'
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)) (FildR PD ρ' τ a)).finrank_eq

theorem multV_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a := by
  rw [multV, multV, finrank_fildR_of_equiv PD e he, finrank_fildR_of_equiv PD e he]

theorem multV_of_le_one (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL (DdRE PD ρ τ)] (h1 : finrank LL (DdRE PD ρ τ) ≤ 1) {b : ℤ}
    (hb : IsJumpV PD ρ τ b) (a : ℤ) : multV PD ρ τ a = if a = b then 1 else 0 := by
  haveI : ∀ a, FiniteDimensional LL (FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  have anti : Antitone (FildR PD ρ τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have mono : ∀ a a', a ≤ a' → finrank LL (FildR PD ρ τ a') ≤ finrank LL (FildR PD ρ τ a) :=
    fun a a' h => Submodule.finrank_mono (anti h)
  have le1 : ∀ a, finrank LL (FildR PD ρ τ a) ≤ 1 := fun a =>
    (Submodule.finrank_mono (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)).trans h1
  have lt : finrank LL (FildR PD ρ τ (b + 1)) < finrank LL (FildR PD ρ τ b) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (anti (by omega)) hb)
  have := le1 a
  have := le1 b
  rw [multV]
  rcases lt_trichotomy a b with h | h | h
  · have := mono (a + 1) b (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have := mono (b + 1) a (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne']
    omega

def transport (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') : Representation LL G V where
  toFun g := e.symm.toLinearMap ∘ₗ ρ' g ∘ₗ e.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V'] [IsScalarTower Qp LL V'] in
theorem transport_apply (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') (g : G) (x : V) :
    e (transport e ρ' g x) = ρ' g (e x) := by
  simp [transport]

end Generic

theorem isCrys_and_multV_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' χ ⟨e, he⟩ cχ cρ
  let f : (Fin 1 → ↥LL.1) ≃ₗ[↥LL.1] ↥LL.1 := LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1
  let ν := transport f (charRep χ)
  have hν : ∀ g x, ν g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • x := fun g x => by
    apply f.injective
    rw [transport_apply, map_smul]
    rfl
  have hρ : ∀ g x, transport e ρ' g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • ρ g x := fun g x => by
    apply e.injective
    rw [transport_apply, he, map_smul]
  have cν : IsCrys (P.PD K) ν :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) f.symm (fun g x => by
      apply f.injective
      rw [transport_apply, f.apply_symm_apply, f.apply_symm_apply]) cχ
  refine ⟨GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) e (transport_apply e ρ')
    ((GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T K LL V ρ _ ν _ hν hρ cν).1 cρ),
    fun τ a b hb => ?_⟩
  obtain ⟨hfin, hle, -⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL ↥LL.1 (charRep χ)).1 τ
  rw [finrank_self] at hle
  rw [← multV_of_equiv (P.PD K) e (transport_apply e ρ')]
  refine GlobalTheory.TwistJump.multV_twist_char l P AI T K LL V ρ _ ν _ hν hρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL _ ν cν).1 τ b (fun c => ?_) a
  rw [multV_of_equiv (P.PD K) f (transport_apply f (charRep χ))]
  exact multV_of_le_one (P.PD K) (charRep χ) τ hle hb c

end GlobalTheory.TwistRepCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShiftStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  first | exact @GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | (intros; apply GlobalTheory.TwistRepCrys.isCrys_and_multV_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataRowBRowEntries
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowBSize

open Classical

theorem ratIn_lt {x y : ℝ} (h : x < y) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) < y := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_left h]
  exact (exists_rat_btwn h).choose_spec.2

theorem ratIn_of_not_lt {x y : ℝ} (h : ¬ x < y) : Formalism.MainNotions.N.ratIn x y = 0 := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_right h]

theorem x_pos' {D : D7} (L : SizeData₂ D) : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

theorem one_le_b' {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem one_le_Lg {D : D7} (L : SizeData₂ D) : 1 ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by
  unfold Formalism.MainNotions.TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem hB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L := by
  unfold Formalism.MainNotions.TwistedPlaces.hB
  have := one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem GP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.GP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := x_pos' L
    have := one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := x_pos' L
    positivity
  unfold Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h3 := L.Sc_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreB_pos {D : D7} (L : SizeData₂ D) {l : ℕ} (hl : 2 ≤ l) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreB L l lam := by
  unfold Formalism.MainNotions.N.coreB
  have hr : (0:ℝ) < D.R.r := by
    have : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hl1 : (0:ℝ) < (l : ℝ) - 1 := by
    have : (2:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) := by
    exact div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)
  have hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) := by
    have := GP_nonneg L; positivity
  have hL := one_le_Lg L
  have hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
      (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
  have hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  positivity

theorem lenRowB_le {D : D7} (L : SizeData₂ D) {C₂ C : ℝ} (hC : 3 * C₂ + 1 ≤ C) {l : ℕ} (hl : 2 ≤ l)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    ((Formalism.MainNotions.N.lenRowB L C₂ l lam : ℚ) : ℝ) ≤ C * Formalism.MainNotions.N.coreB L l lam := by
  have hc := coreB_pos L hl lam
  unfold Formalism.MainNotions.N.lenRowB
  have hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam := by nlinarith
  have := ratIn_lt hlt
  have : (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam :=
    mul_le_mul_of_nonneg_right hC hc.le
  linarith

end GlobalTheory.NLink.RowBSize

theorem GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admB L (tabX L X) C := by
  intro D L P HW X R C hD hR
  intro i _ hrow lam _
  obtain ⟨hI, hA, hO, _⟩ := hrow
  have hl2 : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
  have hC1 : (1:ℝ) ≤ C := hR.2.2.2.2.1
  have hC3 : 3 * R.C₂ + 1 ≤ C := hR.2.2.2.2.2.1
  have hrowB := hD.rowB i hI ⟨hA, hO⟩
  have key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hrowB]
  have hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
      (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd.l i) lam := by
    unfold Formalism.MainNotions.N.coreB; ring
  rw [key, hcore]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    exact GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam
  · have := GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam
    positivity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem starAD_of_global : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK),
    KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D →
    (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ)
      (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
      EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) →
    (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) →
    KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D →
    KillingConditions.StarAD L X := by
  classical
  intro D L HW X R hD hS h09 h78 hG2 hK hSha
  intro i hTw hg hR π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hR' := hR
  obtain ⟨h23, hqd, -⟩ := hR'
  have hsm : D.nd.l i ∉ D.host.small := fun h => h23 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hsm
  have hl3 : D.nd.l i ≠ 3 := fun h => h23 (Or.inr h)
  have hlq : D.nd.l i ≠ D.host.q := fun h => hqd (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hqd (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hodd : Odd (D.nd.l i) := hl.odd_of_ne_two hl2
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hcls : TwistedPlaces.SplitK D (D.nd.l i) ∨ TwistedPlaces.InertK D (D.nd.l i) := by
    unfold TwistedPlaces.SplitK TwistedPlaces.InertK Host.cls primeClass
    simp only [hsm, hlq, hld, if_false]
    split_ifs <;> simp
  rcases hcls with hsp | hin
  ·
    obtain ⟨ep, hdecl, hram, hAdm⟩ := hS.a78 i hTw hg hR hsp
    have hA := hAdm π hπ
    have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inl hsp, fun _ => hram, hg0, hg1⟩
    have hzeta : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := fun v hv => (hA.2.2.2.2.2.1 v (Or.inr hv)).2.2.1 hv
    obtain ⟨-, -, hB⟩ := h78 i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) hA
      (fun _ _ _ => hG2 i hg π hπ) hL hdecl hZ
    have hT := hB hFin hShaT hzeta
    have hpl : (↑((X.dc i).row ∪ (X.dc i).col) : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]
      exact (X.dc i).cover v
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) =
        ((∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ) : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hpl, finsum_mem_coe_finset]
      rw [Finset.sum_congr rfl fun w _ => hD.len0S i hsp π w]
      rw [← Rat.cast_sum]
      congr 1
      simp only [lenA]
      rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
    have hBB := hD.error_bound_split_eq i hsp π
    have hcol : (∑ u ∈ (X.dc i).col,
        ((X.eS i : ℚ) + (N.locDeg D.host.E u : ℚ) * D.R.m * ((X.eS i : ℚ) + D.nd.vdel i) + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + (N.locDeg D.host.E u : ℚ) * D.R.m * (X.eS i : ℚ) + D.R.r * (X.c0 i u : ℚ))) =
        (∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ)) +
        ∑ u ∈ (X.dc i).col, ((N.locDeg D.host.E u : ℚ) * D.R.m * D.nd.vdel i + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + D.R.r * (X.c0 i u : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    unfold EmbeddingTypes.boundSplit at hT
    rw [hcol] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hBB, hVV]
    unfold localErrorBoundPlaces TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith
  ·
    have hA := hS.a09 i hTw hg hR hin π hπ
    have hT := h09 i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) (hS.goodR i) hA hg0 hg1 hZ hFin hShaT
    have hcol := hD.col i hin
    have hrow : (↑(X.dc i).row : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      have := (X.dc i).cover v
      rw [hcol] at this
      simpa using this
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ w ∈ (X.dc i).row, X.lenRow i w : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hrow, finsum_mem_coe_finset, Rat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => hD.len0I i hin π w
    have hW : ∑ w ∈ (X.dc i).row ∪ (X.dc i).col, TruncatedSeriesCountingIdentities.lenW i (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) w =
        ∑ w ∈ (X.dc i).row, X.lenRow i w := by
      rw [hcol, Finset.union_empty]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [TruncatedSeriesCountingIdentities.lenW, hcol]
    rw [hW] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hD.error_bound_inert_eq i hin π, hVV]
    unfold KillingConditions.localErrorBoundDecomposition TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith

end GlobalTheory.NLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheoremsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starInequality_rowsAD_of_global_theorems : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK), KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D → (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) → (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) → KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D → KillingConditions.StarAD L X := by
  first | exact @GlobalTheory.NLink.starAD_of_global | exact GlobalTheory.NLink.starAD_of_global | (intros; apply GlobalTheory.NLink.starAD_of_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.BBSize

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (TwistedPlaces.sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast TwistedPlaces.nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le_two_t (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
  have := D.nd.lPrime i
  have h := LargeLevelLemmas.vdel_le i
  have hs : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i h2
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    rw [Nat.padicValNat_def]
    exact_mod_cast multiplicity_factorial_le (D.nd.l i) D.R.t
  rw [hs] at h
  have : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast this

theorem blk_arith {f t n V large₂ c A k b v h : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 6 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hb0 : 0 ≤ b)
    (hb : b ≤ c * t * n * V * large₂) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) (hh : h ≤ c * t) :
    t * (A * b) + 4 * V * (k + 1) * v + t * k * h ≤ 32 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : t * (A * b) ≤ 6 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * (A * b) ≤ t * ((6 * f) * (c * t * n * V * large₂)) := by gcongr
      _ = _ := by ring
  have h2 : 4 * V * (k + 1) * v ≤ 24 * (c * f * n * t ^ 2 * V * large₂) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (2 * t) := by gcongr; linarith
      _ = 24 * (1 * f * 1 * (t * 1) * V * 1) := by ring
      _ ≤ 24 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : t * k * h ≤ 2 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * k * h ≤ t * k * (c * t) := by gcongr
      _ ≤ t * (2 * f) * (c * t) := by gcongr
      _ = 2 * (c * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem col_arith {f t n V large₂ c A k m r v : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 2 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hm0 : 0 ≤ m) (hm : m ≤ t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) :
    A * (m * v) + k * (2 * v + 2 * (c * r * n * V * large₂)) ≤ 16 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : A * (m * v) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc A * (m * v) ≤ (2 * f) * (t * (2 * t)) := by gcongr
      _ = 4 * (1 * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  have h2 : k * (2 * v) ≤ 8 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (2 * t)) := by gcongr
      _ = 8 * (1 * f * 1 * (t * 1) * 1 * 1) := by ring
      _ ≤ 8 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : k * (2 * (c * r * n * V * large₂)) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * (c * r * n * V * large₂)) ≤ (2 * f) * (2 * (c * t * n * V * large₂)) := by gcongr
      _ = 4 * (c * f * n * (t * 1) * V * large₂) := by ring
      _ ≤ 4 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  rw [mul_add]
  linarith

theorem f_ge_one (D : D7) : (1 : ℝ) ≤ D.R.f := (TwistedPlaces.m_ge_one D).trans (TwistedPlaces.m_le_f D)

theorem nV_ge_one (D : D7) : (1 : ℝ) ≤ D.R.nV := by
  have := TwistedPlaces.t_ge_one D
  have h0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold Ranks.nV
  push_cast
  linarith

theorem blockBoundDeclaration_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) (dc : TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t) :
    (KillingConditions.localErrorBoundDecomposition i dc cB : ℝ) ≤ 32 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hA : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) ≤ 6 * D.R.f := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have := blk_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hA
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg cB) hB (vdel_nonneg i)
    (vdel_le_two_t i h2) hh
  unfold KillingConditions.localErrorBoundDecomposition
  push_cast
  rw [← Finset.sum_mul]
  exact this

theorem blockBoundAtZero_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t)
    (hu : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.n * D.R.nV * TwistedPlaces.large₂ L ∧
      (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L) :
    (localErrorBoundPlaces i ρ π dc c0 cB : ℝ) ≤ 48 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hb := blockBoundDeclaration_le_middleRange L i h2 dc cB hc hB hh
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hk := card_le_sum_locDeg dc.col
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.t_ge D]
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.m_le_k D, TwistedPlaces.k_le_r D]
  have hc' := col_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hcol
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg D.R.m) hmt (Nat.cast_nonneg D.R.r) hrt
    (vdel_nonneg i) (vdel_le_two_t i h2)
  have hs : ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (D.nd.vdel i : ℝ) + 2 * (D.nd.vdel i : ℝ) +
        (Br.h0W i u ρ π : ℝ) + (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ)) +
        (2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L))) := by
    apply Finset.sum_le_sum
    intro u hu'
    obtain ⟨h1, h3⟩ := hu u hu'
    have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) D.R.r)
    linarith
  rw [Finset.sum_add_distrib (f := fun u => (locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ))),
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hs
  unfold KillingConditions.localErrorBoundDecomposition at hb
  unfold localErrorBoundPlaces
  push_cast at hb ⊢
  linarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  intro D L _ HW X R c hc hD hJ i hi hg hR π hπ
  obtain ⟨hB, hh, hS⟩ := hJ i hi hg hR
  have h2 : D.nd.l i ∉ D.host.small := fun h => hR.1 (Or.inl h)
  have hq : D.nd.l i ≠ D.host.q := fun h => hR.2.1 (Or.inl h)
  have hd : D.nd.l i ≠ D.host.d := fun h => hR.2.1 (Or.inr h)
  have hL := TwistedPlaces.L_ge_one L
  have hM0 : 0 ≤ c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ TwistedPlaces.large₂ L := by linarith
    positivity
  have hM := le_mul_of_one_le_right hM0 hL
  have hE : 60 * c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 =
      60 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L * TwistedPlaces.large₂ L) := by ring
  rw [hE]
  rcases TwistedPlaces.split_or_inert D h2 hq hd with hs | hin
  · rw [hD.error_bound_split_eq i hs π]
    have := blockBoundAtZero_le_middleRange L i h2 (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) hc hB hh
      (fun u hu => ⟨(hS hs u hu).1, (hS hs u hu).2 π hπ⟩)
    linarith
  · rw [hD.error_bound_inert_eq i hin π]
    have := blockBoundDeclaration_le_middleRange L i h2 (X.dc i) (X.cB i) hc hB hh
    linarith

end GlobalTheory.NLink.BBSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRangeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonPlacePart_localBound_le_middleRange : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  first | exact @GlobalTheory.NLink.BBSize.main | exact GlobalTheory.NLink.BBSize.main | (intros; apply GlobalTheory.NLink.BBSize.main <;> assumption)
end
end

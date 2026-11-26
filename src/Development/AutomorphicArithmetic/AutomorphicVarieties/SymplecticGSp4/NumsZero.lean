module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.H1cZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.h1cZero :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → K.Normal → ∀ (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ), (∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) → K ≤ γ.ker → (∀ v ∈ T, ∃ g ∈ Dec (F := ℚ) (pl v), γ g ≠ 1) → Van T pl K γ → (galFrame SP T Q v0 pl K).H1c ρ = ⊥ := by
  intro Ω _ _ _ l SP T Q v0 pl K hD hK k _ M _ _ ρ γ hρ hKγ hT hV
  rw [eq_bot_iff]
  rintro ⟨c, b⟩ ⟨h1, h2, h3, h4, h5⟩
  have h3' : ∀ q : Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → c (toGS Ω SP g) = 0 := by
    intro q g hg hgK
    exact h3 q ⟨g, Ine_le_Dec _ hg⟩ (Subgroup.mem_subgroupOf.2 ⟨hg, hgK⟩)
  have h4' : ∀ v : T, ∀ g ∈ Dec (F := ℚ) (pl v), c (toGS Ω SP g) = (γ g : k) • b v - b v := by
    intro v g hg
    rw [← hρ]
    exact h4 v ⟨g, hg⟩
  have h5' : b v0 = 0 := h5
  obtain ⟨S, e, hS, -, hTp, hQ⟩ := galIdx Ω l v0 hD
  have hcont : Continuous (toGS Ω SP) := continuous_quot_mk
  have hc : ∀ g, c (toGS Ω SP g) = 0 := by
    intro g
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun f => ?_
    have hz : ∀ g h, f (c (toGS Ω SP (g * h))) = f (c (toGS Ω SP g)) + (γ g : k) * f (c (toGS Ω SP h)) := by
      intro g h
      have := h2 (toGS Ω SP g) (toGS Ω SP h)
      simp only at this
      rw [map_mul, this, hρ, map_add (f := _), map_smul, smul_eq_mul]
    have hu := unrOf Ω k γ K hKγ SP T (fun s => f (c s)) hz (by
      intro v hv
      obtain ⟨y, hy⟩ := e.surjective ⟨v, by rw [hS] at hv; exact hv⟩
      have hv' : (e y).1 = v := congrArg Subtype.val hy
      rcases y with t | q
      · have h := hTp t ((t.1 : ℕ) : 𝓞 ℚ)
        have e' : algebraMap ℚ Ω (((t.1 : ℕ) : 𝓞 ℚ) : ℚ) = ((t.1 : ℕ) : Ω) := by simp
        rw [e', hv'] at h
        exact Or.inl ⟨t.1, t.2, h.1 (hD.isOver _ (Or.inl t.2))⟩
      · refine Or.inr ⟨pl q, hv' ▸ hQ q, fun g hg hgK => ?_⟩
        simp only [h3' q g hg hgK, map_zero])
    obtain ⟨m, hm⟩ := hV (fun g => f (c (toGS Ω SP g))) ((h1.comp_continuous hcont).comp f) hz hu (by
      intro v hv
      refine ⟨f (b ⟨v, hv⟩), fun g hg => ?_⟩
      simp only [h4' ⟨v, hv⟩ g hg, map_sub, map_smul, smul_eq_mul])
    obtain ⟨g0, hg0, hne⟩ := hT v0 v0.2
    have h0 := hm g0
    simp only [h4' v0 g0 hg0, h5', smul_zero, sub_zero, map_zero] at h0
    have hm0 : m = 0 := by
      have : ((γ g0 : k) - 1) * m = 0 := by rw [sub_mul, one_mul]; exact h0.symm
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
    have := hm g
    simpa [hm0] using this
  refine (Submodule.mem_bot k).2 (Prod.ext (funext fun s => ?_) (funext fun v => ?_))
  · obtain ⟨g, rfl⟩ : ∃ g, toGS Ω SP g = s := QuotientGroup.mk_surjective s
    exact hc g
  · obtain ⟨g0, hg0, hne⟩ := hT v.1 v.2
    have h0 := h4' v g0 hg0
    rw [hc] at h0
    have : ((γ g0 : k) - 1) • b v = 0 := by rw [sub_smul, one_smul]; exact h0.symm
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpAct
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem ps_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (i : Fin 4) (g : G ℚ Ω) : D.ps i g = D.al g ^ lamW i * D.Psi g ^ muW i := by
  fin_cases i <;> simp [Raw.ps, Raw.th, lamW, muW]

private theorem rbar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (g : G ℚ Ω) : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Raw.rbar, Raw.r0, mapRep, diagRep]
  · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]

theorem UpperTheory.V.X.spAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ) (g : G ℚ Ω) (Y : (form c.O).gw (ResidueField c.O) j), Alg.FormData.adRep h j (toGS Ω D.SP g) Y = Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g • Y := by
  intro Ω _ _ _ l _ c D rb hrb h j g Y
  apply Subtype.ext
  show rb (toGS Ω D.SP g) * (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) * rb (toGS Ω D.SP g)⁻¹ = _
  rw [← map_inv, ← MonoidHom.comp_apply rb, ← MonoidHom.comp_apply rb, hrb, rbar_eq, rbar_eq]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : w4 a - w4 b = j
  · have key : D.ps a g * D.ps b g⁻¹ = (D.al ^ j.1 * D.Psi ^ j.2) g := by
      subst hab
      rw [map_inv, ps_eq, ps_eq, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.zpow_apply]
      simp only [w4, Prod.fst_sub, Prod.snd_sub, zpow_sub, div_eq_mul_inv, mul_inv]
      ac_rfl
    rw [Raw.bar, ← key, Units.val_mul, map_mul]
    ring
  · have hz : (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) a b = 0 := (Submodule.mem_inf.1 Y.2).2 a b hab
    simp [hz]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpDim
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

section
variable (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k]

private theorem spDim_JR : (form O).JR k = J4 k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Alg.FormData.JR, form, J4]

private theorem spDim_mem (j : ℤ × ℤ) (Y : M4 k) : Y ∈ (form O).gw k j ↔
    (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) ∧
      ∀ a b, wt a b ≠ j → Y a b = 0 := by
  have e : Y ∈ (form O).gw k j ↔ (Y.transpose * (form O).JR k + (form O).JR k * Y = 0 ∧
      ∀ a b, (form O).blk a ≠ (form O).blk b → Y a b = 0) ∧ ∀ a b, wt a b ≠ j → Y a b = 0 := Iff.rfl
  rw [e, spDim_JR]
  refine and_congr_left fun _ => ⟨fun ⟨h, _⟩ => ?_, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨?_, fun a b h => absurd rfl h⟩⟩
  · have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 0) 2
    have h3 := congrFun (congrFun h 0) 3
    have h4 := congrFun (congrFun h 1) 2
    have h5 := congrFun (congrFun h 1) 3
    have h6 := congrFun (congrFun h 2) 3
    simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5
    · linear_combination -h6
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, h1, h2, h3, h4, h5, h6]

private theorem spDim_one (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hB : B ∈ (form O).gw k j) (hab : B a b = 1)
    (h : ∀ Y ∈ (form O).gw k j, Y a b = 0 → Y = 0) : finrank k ((form O).gw k j) = 1 := by
  refine finrank_eq_one (⟨B, hB⟩ : (form O).gw k j) ?_ ?_
  · intro e
    have : B = 0 := congrArg Subtype.val e
    rw [this] at hab
    simp at hab
  · intro Y
    refine ⟨Y.1 a b, Subtype.ext ?_⟩
    have := h (Y.1 a b • B - Y.1) (Submodule.sub_mem _ (Submodule.smul_mem _ _ hB) Y.2) (by simp [hab])
    exact sub_eq_zero.mp this

private theorem spDim_root (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hj : wt a b = j)
    (hB : B ∈ (form O).gw k (wt a b)) (hab : B a b = 1)
    (h : ∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
      Y a b = 0 → Y b.rev a.rev = 0)
    (h' : ∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) :
    finrank k ((form O).gw k j) = 1 := by
  subst hj
  refine spDim_one O k _ B a b hB hab fun Y hY h0 => ?_
  obtain ⟨y1, y2⟩ := (spDim_mem O k _ Y).1 hY
  ext c d
  by_cases e : wt c d = wt a b
  · rcases h' c d e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h0
    · exact h Y y1 h0
  · exact y2 c d e

private theorem spDim_zero : finrank k ((form O).gw k 0) = 2 := by
  let f : (form O).gw k 0 →ₗ[k] k × k :=
    { toFun := fun Y => (Y.1 0 0, Y.1 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro Y hY
      have h0 : Y.1 0 0 = 0 := congrArg Prod.fst hY
      have h1 : Y.1 1 1 = 0 := congrArg Prod.snd hY
      obtain ⟨⟨-, -, y3, y4, -, -⟩, y2⟩ := (spDim_mem O k _ Y.1).1 Y.2
      ext c d
      by_cases e : c = d
      · subst e
        fin_cases c <;> simp [h0, h1, y3, y4]
      · exact y2 c d fun n => e ((wt_eq_zero c d).1 n)
    · rintro ⟨x, y⟩
      refine ⟨⟨Matrix.diagonal ![x, y, -y, -x], (spDim_mem O k _ _).2 ⟨by simp, fun a b h => ?_⟩⟩, ?_⟩
      · exact Matrix.diagonal_apply_ne _ fun n => h ((wt_eq_zero a b).2 n)
      · rfl
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

private theorem spDim_B (a b : Fin 4) (B : M4 k)
    (h : B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2)
    (h' : ∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) : B ∈ (form O).gw k (wt a b) := by
  refine (spDim_mem O k _ _).2 ⟨h, fun c d e => h' c d ?_ ?_⟩
  · rintro ⟨rfl, rfl⟩; exact e rfl
  · rintro ⟨rfl, rfl⟩; exact e (wt_rev _ _)

end

theorem UpperTheory.V.X.spDim :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k] (j : ℤ × ℤ), finrank k ((form O).gw k j) = dimP j := by
  intro O _ k _ _ j
  unfold dimP
  split_ifs with h0 hw
  · subst h0; exact spDim_zero O k
  · have key : ∀ (a b : Fin 4) (B : M4 k), wt a b = j → B a b = 1 →
        (B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2) →
        (∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) →
        (∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
          Y a b = 0 → Y b.rev a.rev = 0) →
        (∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) → finrank k ((form O).gw k j) = 1 :=
      fun a b B e h1 h2 h3 h4 h5 => spDim_root O k j B a b e (spDim_B O k a b B h2 h3) h1 h4 h5
    simp only [wts, oddRoots, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · refine key 0 1 !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 3 = 0
        simp [*]
    · refine key 1 0 !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 2 = 0
        simp [*]
    · refine key 1 2 !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 2 = 0
        simp [*]
    · refine key 2 1 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 1 = 0
        simp [*]
    · refine key 0 3 !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 0 3 = 0
        simp [*]
    · refine key 3 0 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 0 = 0
        simp [*]
    · refine key 0 2 !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 3 = 0
        simp [*]
    · refine key 2 0 !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 1 = 0
        simp [*]
    · exact absurd rfl h0
  · rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro Y hY
    obtain ⟨-, y2⟩ := (spDim_mem O k _ Y).1 hY
    ext c d
    exact y2 c d fun n => hw (n ▸ wt_mem c d)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcScalDim
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.scalDim :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k Γ M) (γ χ : Γ →* kˣ), (∀ g m, ρ g m = (γ g : k) • m) → (∀ σ, γ σ = 1 → finrank k (LinearMap.ker (ρ σ - 1)) = finrank k M) ∧ (∀ σ, (finrank k M = 0 ∨ γ σ ≠ 1) → finrank k (LinearMap.ker (ρ σ - 1)) = 0) ∧ ((finrank k M = 0 ∨ ∃ g, γ g ≠ χ g) → finrank k (Loc.H0dual χ ρ) = 0) := by
  intro k Γ M _ _ _ _ _ ρ γ χ h
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun hσ => ?_⟩
  · have : LinearMap.ker (ρ σ - 1) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      simp [h, hσ]
    rw [this, finrank_top]
  · have : LinearMap.ker (ρ σ - 1) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      rw [Submodule.mem_bot]
      rcases hσ with h0 | h0
      · exact (finrank_zero_iff_forall_zero.mp h0) m
      · have h1 : ((γ σ : k) - 1) • m = 0 := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, h] at hm
          rw [sub_smul, one_smul]
          exact hm
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact absurd (Units.ext (sub_eq_zero.mp h2)) h0
        · exact h2
    rw [this, finrank_bot]
  · have : Loc.H0dual χ ρ = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_bot]
      ext m
      rcases hσ with h0 | ⟨g, hg⟩
      · rw [(finrank_zero_iff_forall_zero.mp h0) m]; simp
      · have h1 := hf g m
        rw [h, map_smul, smul_eq_mul] at h1
        have h2 : ((γ g : k) - χ g) * f m = 0 := by
          rw [sub_mul, h1]; simp
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Units.ext (sub_eq_zero.mp h3)) hg
        · simpa using h3
    rw [this, finrank_bot]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem nums_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) {j : ℤ × ℤ} (hj : j ∈ oddRoots) :
    D.XVan (D.al ^ j.1 * D.Psi ^ j.2) ∧ (j.1 = 1 ∨ j.1 = -1) ∧
      ∃ a b, lamW a ≠ lamW b ∧ D.al ^ j.1 * D.Psi ^ j.2 * D.ps b = D.ps a := by
  have h1 := hD.xvan D.al (by simp)
  have h2 := hD.xvan D.be (by simp)
  have h3 := hD.xvan D.th (by simp)
  simp only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : D.al ^ wAl.1 * D.Psi ^ wAl.2 = D.al := by simp [wAl]
    rw [e]
    exact ⟨h1.1, by decide, 2, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wAl).1 * D.Psi ^ (-wAl).2 = D.al⁻¹ := by simp [wAl]
    rw [e]
    exact ⟨h1.2, by decide, 3, 2, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ wBe.1 * D.Psi ^ wBe.2 = D.be := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.1, by decide, 1, 2, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ (-wBe).1 * D.Psi ^ (-wBe).2 = D.be⁻¹ := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.2, by decide, 2, 1, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ wTh.1 * D.Psi ^ wTh.2 = D.th := by simp [wTh, Raw.th]
    rw [e]
    exact ⟨h3.1, by decide, 0, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wTh).1 * D.Psi ^ (-wTh).2 = D.th⁻¹ := by simp [wTh, Raw.th, mul_comm]
    rw [e]
    exact ⟨h3.2, by decide, 3, 0, by decide, by simp [Raw.ps]⟩

private theorem nums_lc {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem nums_gen (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k] [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (hd : Module.finrank k M = 0 ∨ ∃ g, γ g ≠ X.cycK Ω l k g) :
    Module.Finite k ((X.galFrame SP T Q v0 pl K).Ob ρ) ∧
      (γ σ = 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ) + Module.finrank k M) ∧
      (Module.finrank k M = 0 ∨ γ σ ≠ 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ)) := by
  have hlc : ∀ m, IsLocallyConstant fun g => ρ g m := fun m s =>
    (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (by
      have := ((nums_lc γ (Subgroup.isOpen_mono hKγ hK)).comp fun u => (u : k) • m) s
      simp only [Function.comp_def, ← hγ] at this
      exact this)
  obtain ⟨c1, -, c3⟩ := X.galCount ⟨P.loc.lf, P.loc.lt, P.loc.le, P.gf, P.ge, P.pt⟩ Ω l v0 hG k M
    ρ hlc (fun q _ g _ hg => LinearMap.ext fun m => by
      rw [hγ, show γ g = 1 from hKγ hg]; simp) σ hσ
  obtain ⟨s1, s2, s3⟩ := X.scalDim (ρ.comp (toGS Ω SP)) γ (X.cycK Ω l k) hγ
  rw [s3 hd, add_zero] at c3
  exact ⟨c1, fun e => c3.trans (congrArg _ (s1 σ e)), fun e => c3.trans (congrArg _ (s2 σ e))⟩

private theorem nums_zero {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] (F : Frame Γ) (ρ : Representation k Γ M) (h : Module.finrank k M = 0) :
    Module.finrank k (F.H1c ρ) = 0 := by
  haveI : Subsingleton M := Module.finrank_zero_iff.1 h
  exact Module.finrank_zero_of_subsingleton

private theorem nums_all (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hN : K.Normal) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k]
    [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (k1 : X.cycK Ω l k σ = -1) (j : ℤ × ℤ) (hdim : Module.finrank k M = dimP j) (hcc : γ σ = (-1) ^ j.1)
    (sg : ℕ → G ℚ Ω) (hsg : ∀ v ∈ T, sg v ∈ Dec (F := ℚ) (pl v)) (e1 : X.cycK Ω l k (sg l) = 1)
    (hodd : j ∈ oddRoots → X.Van T pl K γ ∧ ∀ v ∈ T, γ (sg v) ≠ 1)
    (F : Frame (GS Ω SP)) (hF : F = X.galFrame SP T Q v0 pl K) :
    Module.Finite k (F.Ob ρ) ∧
    Module.finrank k (F.Ob ρ) = Module.finrank k (F.H1c ρ) + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank k (F.H1c ρ) = 0) := by
  subst hF
  have h2 : (-1 : kˣ) ≠ 1 := fun e => by
    have e' : ((2 : ℕ) : k) = 0 := by
      have := congrArg Units.val e
      simp only [Units.val_neg, Units.val_one] at this
      push_cast
      linear_combination -this
    exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 e'))
  have key := nums_gen P v0 hG hK ρ γ hγ hKγ hσ
  by_cases hj : j = 0 ∨ j = wPs ∨ j = -wPs
  · have e : γ σ = 1 := by
      rw [hcc]
      rcases hj with rfl | rfl | rfl <;> simp [wPs]
    obtain ⟨a1, a2, -⟩ := key (Or.inr ⟨σ, by rw [e, k1]; exact h2.symm⟩)
    refine ⟨a1, ?_, fun n1 n2 n3 => by tauto⟩
    rw [a2 e, hdim]
    congr 1
    rcases hj with rfl | rfl | rfl <;> decide
  rw [if_neg fun e => hj (Or.inl e), if_neg fun e => hj (Or.inr e), add_zero]
  by_cases ho : j ∈ oddRoots
  · obtain ⟨o1, hne⟩ := hodd ho
    have o2 : ∀ j ∈ oddRoots, j.1 = 1 ∨ j.1 = -1 := by decide
    have e : γ σ ≠ 1 := by
      rw [hcc]
      rcases o2 j ho with o | o <;> rw [o] <;> simpa using h2
    obtain ⟨a1, -, a2⟩ := key (Or.inr ⟨sg l, e1 ▸ hne l hG.l_mem⟩)
    refine ⟨a1, a2 (Or.inr e), fun _ _ _ => ?_⟩
    rw [X.h1cZero Ω l v0 hG hN _ _ ρ γ hγ hKγ (fun v hv => ⟨sg v, hsg v hv, hne v hv⟩) o1, finrank_bot]
  · have e : j ∉ wts := by
      simp only [wts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [dimP, if_neg fun e => hj (Or.inl e), if_neg e] at hdim
    obtain ⟨a1, -, a2⟩ := key (Or.inl hdim)
    exact ⟨a1, a2 (Or.inl hdim), fun _ _ _ => nums_zero _ _ hdim⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.nums :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → D.Nums := by
  intro Ω _ _ _ l hl c D hD P
  obtain ⟨-, f2, -, -, -, -, -, ⟨fc, -⟩, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hN, hI, hK⟩ := X.spKer D
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0)
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  have hTS : D.T ⊆ D.S := Finset.insert_subset hD.l_mem (by
    classical
    exact Finset.filter_subset _ _)
  have hU : ∀ p, (p ∈ D.T ∨ p ∈ D.S \ D.T) ↔ p ∈ D.S := fun p => by
    rw [← Finset.mem_union, Finset.union_sdiff_of_subset hTS]
  have hG : X.GalData l D.SP D.T (D.S \ D.T) D.pl D.rbar.ker :=
    ⟨hD.l_odd, fun p hp => hD.S_prime p ((hU p).1 hp), Finset.disjoint_sdiff, D.residueChar_mem_levelPrimes,
      fun v => exists_congr fun p => by rw [hU], fun p hp => hD.pl_over p (hD.S_prime p ((hU p).1 hp)),
      fun q _ hq => hI (hq.trans (Subgroup.relIndex_dvd_index_of_normal _ _))⟩
  obtain ⟨k1, k2⟩ := X.cycKFacts Ω l (ResidueField c.O)
  intro rb hrb h j
  let γ : G ℚ Ω →* (ResidueField c.O)ˣ := (Units.map (residue c.O).toMonoidHom).comp (D.al ^ j.1 * D.Psi ^ j.2)
  have hγ : ∀ g m, FormData.adRep h j (toGS Ω D.SP g) m = (γ g : ResidueField c.O) • m := X.spAct D rb hrb h j
  have hKγ : D.rbar.ker ≤ γ.ker := fun g hg => Units.ext (hK j g hg)
  have hdim := X.spDim c.O (ResidueField c.O) j
  have hcc : γ D.cc = (-1) ^ j.1 := by
    show Units.map (residue c.O).toMonoidHom (D.al D.cc ^ j.1 * D.Psi D.cc ^ j.2) = _
    rw [fc, hD.Psi_even, one_zpow, mul_one, map_zpow]
    congr 1
  have e1 : X.cycK Ω l (ResidueField c.O) (D.sg l) = 1 :=
    Units.ext ((k2 c (residue c.O) _).trans ((hD.om_bar _).symm.trans (f2 l D.residueChar_mem_levelPrimes).2.1))
  have hodd : j ∈ oddRoots → X.Van D.T D.pl D.rbar.ker γ ∧ ∀ v ∈ D.T, γ (D.sg v) ≠ 1 := fun ho => by
    obtain ⟨o1, -, a, b, hab, o3⟩ := nums_odd D hD ho
    refine ⟨fun z hz hc hu hT => o1 z hz hc (fun A hA g hg hk => hu A hA g hg hk) hT, fun v hv e => ?_⟩
    refine (f2 v hv).2.2 a b hab ?_
    have e' : Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) = 1 := congrArg Units.val e
    rw [← o3]
    show residue c.O (((D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) : c.O) * (D.ps b (D.sg v) : c.O)) = _
    rw [map_mul]
    exact (congrArg (· * _) e').trans (one_mul _)
  have hF : D.frame = X.galFrame D.SP D.T (D.S \ D.T) ⟨l, D.residueChar_mem_levelPrimes⟩ D.pl D.rbar.ker := by
    unfold Raw.frame X.galFrame
    rfl
  exact nums_all P ⟨l, D.residueChar_mem_levelPrimes⟩ hG hN fo (FormData.adRep h j) γ hγ hKγ hD.isCC (k1 _ hD.isCC) j hdim hcc D.sg
    (fun v hv => (f2 v hv).1) e1 hodd D.frame hF

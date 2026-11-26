module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.ProjectionComponents.CompOfProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnifLtOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.AutomorphicInSphericalLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.EigGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.BridgeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.LocSubD

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RepsEx
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trim {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (y : DA Δ) (hy : D.Off y) :
    ∃ t w : DA Δ, w ∈ D.U2 ∧ t * w = y ∧ D.Off t ∧ {v | t.1 v ≠ 1}.Finite := by
  classical
  let P : Pl F → Prop := fun v => y.1 v ∈ KD ((cv v) Δ) (Ov v) ∧ v ∉ D.Sg
  have hfin : {v | y.1 v ∉ KD ((cv v) Δ) (Ov v)}.Finite := Filter.eventually_cofinite.mp y.2
  have hbad : {v | ¬ P v}.Finite := by
    refine (hfin.union D.Sg.finite_toSet).subset ?_
    intro v hv
    by_cases h1 : y.1 v ∈ KD ((cv v) Δ) (Ov v)
    · exact Or.inr (by_contra fun h2 => hv ⟨h1, h2⟩)
    · exact Or.inl h1
  refine ⟨⟨fun v => if P v then 1 else y.1 v, ?_⟩, ⟨fun v => if P v then y.1 v else 1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Filter.eventually_cofinite.mpr (hbad.subset ?_)
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) ∈ KD ((cv v) Δ) (Ov v)
    rw [if_pos h]
    exact one_mem _
  · show ∀ᶠ v in Filter.cofinite, (if P v then y.1 v else 1) ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : P v
    · rw [if_pos h]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · simp only [Dat.U2, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show (if P v then y.1 v else 1) ∈ D.J2v v
    by_cases h : P v
    · rw [if_pos h, Dat.J2v, if_neg h.2]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · refine Subtype.ext (funext fun v => ?_)
    show (if P v then 1 else y.1 v) * (if P v then y.1 v else 1) = y.1 v
    split_ifs <;> simp
  · intro v hv
    show (if P v then 1 else y.1 v) = 1
    split_ifs
    · rfl
    · exact hy v hv
  · refine hbad.subset ?_
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) = 1
    rw [if_pos h]

theorem UpperTheory.V.Z.Sym.So.repsEx :
    UpperTheory.V.Z.Sym.So.RepsEx := by
  intro F _ _ Δ A hA hCR ι hι
  classical
  obtain ⟨Y, hY, hdec⟩ := hCR F Δ A.dat (datOk F Δ A hA).1 ι hι
  let f : DA Δ → DA Δ := fun y => if h : A.dat.Off y then (trim A.dat y h).choose else y
  refine ⟨Y.image f, ?_, ?_⟩
  · intro y' hy'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨w, -, -, ht, hfin⟩ := (trim A.dat y (hY y hy)).choose_spec
    simp only [f, dif_pos (hY y hy)]
    exact ⟨ht, hfin⟩
  · intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hdec g
    obtain ⟨w, hw, hty, -, -⟩ := (trim A.dat y (hY y hy)).choose_spec
    refine ⟨γ, s, hs, f y, Finset.mem_image_of_mem f hy, w * u, mul_mem hw hu, ?_⟩
    simp only [f, dif_pos (hY y hy)]
    conv_lhs => rw [← hty]
    simp only [mul_assoc]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CongLev
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_J_of_cong (V : Lev k) {n : ℕ} (g : GL (Fin n) k)
    (h : ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ (V.c + 1)) : g ∈ V.J n := by
  have hu : uniformizer k ^ (V.c + 1) < 1 := pow_lt_one₀ zero_le' uniformizer_lt_one (Nat.succ_ne_zero _)
  have e : ∀ i, valuation k (g.val i i) = 1 := fun i => by
    have h1 : valuation k (g.val i i - 1) < 1 := by
      have := h i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      exact this.trans_lt hu
    have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  refine (Sig.memJ k V n g).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact (e i).le
    · have := h i j
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at this
      exact (this.trans_lt hu).le
  · have := h i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
    rwa [GlAx.unif_spec]
  · have h0 : g.val i i ≠ 0 := fun h0 => by
      have := e i
      simp [h0] at this
    refine ⟨Units.mk0 _ h0, V.le (mem_Uc.2 ⟨e i, ?_⟩), rfl⟩
    have := h i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
    rwa [zpow_natCast]

private theorem proj_int {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) {Δ s : k} (hs : s * s = Δ)
    (a : Lsq k Δ) (ha : IsIntegral O a) : valuation k (proj hs a) ≤ 1 := by
  have hv : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩
  have h : IsIntegral O (proj hs a) := ha.map_of_comp_eq (RingHom.id O) (proj hs) (by
    ext x
    have e : algebraMap O (Lsq k Δ) x = ⟨algebraMap O k x, 0⟩ := rfl
    simp [proj, e])
  exact hv.mem_of_integral h

end Loc

private theorem mem_KD {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} (x : DX Δ) (hd : (mt x).det = 1)
    (hi : ∀ i j, IsIntegral O (mt x i j)) : x ∈ KD Δ O := by
  let X : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt x i j, hi i j⟩
  have hX : X.det = 1 := Subtype.ext (by
    have h := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) X
    refine h.trans ?_
    exact hd)
  exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mk'' X (by rw [hX]; exact isUnit_one), Units.ext (Matrix.ext fun i j => rfl)⟩

private theorem det_conj {K : Type} [Field K] {Δ : K} (a b : DX Δ) (h : (mt b).det = 1) : (mt (a⁻¹ * b * a)).det = 1 := by
  have e : mt (a⁻¹ * b * a) = mt a⁻¹ * mt b * mt a := rfl
  have e2 : mt a⁻¹ * mt a = 1 := by
    show mt (a⁻¹ * a) = 1
    rw [inv_mul_cancel]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, h, mul_one, ← Matrix.det_mul, e2, Matrix.det_one]

private theorem val_norm {F : Type} [Field F] [NumberField F] (v : Pl F) :
    valuation (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) ≤ uniformizer (Kv v) := by
  rw [le_uniformizer_iff]
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  have h2 : (Valued.v : Valuation (Kv v) _) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) < 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : F)
    have e2 : ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) = algebraMap F (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : F) := (map_natCast _ _).symm
    rw [e2]
    refine e.trans_lt ?_
    change v.valuation F (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) < 1 at h
    rw [map_natCast] at h
    exact h
  haveI : (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he : (valuation (Kv v)).IsEquiv (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))) := isEquiv _ _
  simp only [← not_le] at h2 ⊢
  exact fun h3 => h2 (he.one_le_iff_one_le.1 h3)

private theorem eD_sub {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (x : DX Δ) (i j : Fin 2) :
    ((eD hs x).val - 1) i j = proj hs ((mt x - 1) i j) := by
  have e : (eD hs x).val i j = proj hs (mt x i j) := rfl
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem nat_int {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (n : ℕ) : IsIntegral O (n : R) := by
  simpa using isIntegral_algebraMap (R := O) (A := R) (x := (n : O))

private def nrm {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : ℕ :=
  ∏ v ∈ A.Sg, Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)

private theorem mem_lvS_of_congruence {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) (hA : A.Ok) (y : DA Δ) (g : SA Δ)
    (key : ∀ (v : Pl F) (i j : Fin 2), ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j =
      (nrm A : Lsq (Kv v) (cv v Δ)) * a) : g ∈ A.lvS y := by
  obtain ⟨-, -, hInt, -, hU2⟩ := datOk _ _ A hA
  have hg1 : ∀ v, (mt ((g : DA Δ).1 v)).det = 1 := fun v => by
    have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 g.2 v)
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have e : (MulAut.conj y⁻¹).toMonoidHom (g : DA Δ) = y⁻¹ * g * y := by simp
  rw [SD.lvS, Subgroup.mem_subgroupOf, Subgroup.mem_comap, e, hU2]
  refine ⟨fun v hv => mem_J_of_cong _ _ fun i j => ?_, fun v hv => mem_KD _ ?_ fun i j => ?_⟩
  · obtain ⟨a, ha, e1⟩ := key v i j
    obtain ⟨r, hr⟩ : Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1) ∣ nrm A :=
      Finset.dvd_prod_of_mem (fun v => Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)) hv
    rw [eD_sub, e1, map_mul, map_natCast, map_mul, hr, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    have h1 : valuation (Kv v) ((r : ℕ) : Kv v) ≤ 1 := natCast_mem (valuation (Kv v)).integer r
    have h2 := proj_int (hInt v hv).1 (A.hs v hv) a ha
    calc _ ≤ uniformizer (Kv v) ^ ((A.V v).c + 1) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (pow_le_pow_left' (val_norm v) _) h1) h2
      _ = _ := by simp
  · exact det_conj _ _ (hg1 v)
  · obtain ⟨a, ha, e1⟩ := key v i j
    have e2 : mt ((y⁻¹ * g * y : DA Δ).1 v) i j = (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j + (1 : Matrix (Fin 2) (Fin 2) _) i j := by
      simp
    rw [e2, e1]
    refine IsIntegral.add (IsIntegral.mul (nat_int _) ha) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]

private theorem mem_under {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (N : ℕ)
    (hN : (N : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (N : 𝓞 L) ∈ w.asIdeal := by
  have h2 := Ideal.mem_comap.1 hN
  simpa using h2

private theorem norm_ne {F : Type} [Field F] [NumberField F] (v : Pl F) : Ideal.absNorm v.asIdeal ≠ 0 :=
  fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

private theorem nrm_ne {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : nrm A ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (norm_ne v)

private theorem mem_of_dvd {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (M : ℕ)
    (h : Ideal.absNorm (un w).asIdeal ∣ M) : ((3 * M : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  obtain ⟨q, rfl⟩ := h
  refine mem_under w _ ?_
  rw [Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

private theorem entry_mono {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (z : Kw w) (a q : ℕ)
    (h : ∃ b ∈ w.adicCompletionIntegers L, z = ((3 * (a * q) : ℕ) : Kw w) * b) :
    ∃ b ∈ w.adicCompletionIntegers L, z = (a : Kw w) * b := by
  obtain ⟨b, hb, e⟩ := h
  refine ⟨(3 * q : ℕ) * b, mul_mem (natCast_mem _ _) hb, ?_⟩
  rw [e]
  push_cast
  ring

private theorem abs_lev {α β γ υ σ : Type} (Y : Finset α) (p : α → β → Prop) (hY : ∀ y ∈ Y, {v | ¬ p y v}.Finite)
    (b : β → ℕ) (hb : ∀ v, b v ≠ 0) (un : γ → β) (mem : ℕ → γ → Prop) (hmem : ∀ w M, b (un w) ∣ M → mem (3 * M) w)
    (C : ℕ → υ → Prop) (D : υ → σ → Prop) (E : α → σ → Prop)
    (h : ∀ y, ∃ a, a ≠ 0 ∧ ∀ q U, C (3 * (a * q)) U → ∀ g, D U g → E y g) :
    ∃ m : ℕ, 3 ≤ m ∧ (∀ w, ¬ mem m w → ∀ y ∈ Y, p y (un w)) ∧ ∀ U, C m U → ∀ y ∈ Y, ∀ g, D U g → E y g := by
  classical
  choose a ha hE using h
  let P : Finset β := (Set.Finite.biUnion Y.finite_toSet hY).toFinset
  let M : ℕ := (∏ y ∈ Y, a y) * ∏ v ∈ P, b v
  have hM : 0 < M := Nat.pos_of_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => ha y)
    (Finset.prod_ne_zero_iff.2 fun v _ => hb v))
  refine ⟨3 * M, Nat.le_mul_of_pos_right 3 hM, fun w hw y hy => ?_, fun U hU y hy g hg => ?_⟩
  · by_contra hne
    have hv : un w ∈ P := (Set.Finite.mem_toFinset _).2 (Set.mem_biUnion hy hne)
    exact hw (hmem w M (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hv) _))
  · obtain ⟨q, hq⟩ : a y ∣ M := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hy) _
    rw [hq] at hU
    exact hE y q U hU g hg

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Ov DX KD RP SA Lsq

theorem UpperTheory.V.Z.Sym.So.congLev :
    UpperTheory.V.Z.Sym.So.CongLev := by
  intro L _ _ _ B hB _ _ _ A hA _ Y hY
  refine abs_lev Y _ hY (fun v => Ideal.absNorm v.asIdeal) norm_ne un _ (fun w M h => mem_of_dvd w M h) _ _ _ fun y => ?_
  exact (hB.cong y (nrm A) (nrm_ne A)).elim fun a h => ⟨a, h.1, fun q U hU g hg =>
    mem_lvS_of_congruence A hA y g fun v => h.2 g v fun w _ i j => entry_mono w _ _ _ (((hU _).1 hg).2 w i j)⟩

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LevExt
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Gen
variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') :
    Sig.eD h = Sig.eD h' := by
  subst e; rfl

private theorem mem_lvS (A : SD Δ) (y : DA Δ) (g : SA Δ) :
    g ∈ A.lvS y ↔ y⁻¹ * (g : DA Δ) * y ∈ A.dat.U2 := by
  unfold SD.lvS
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  show (MulAut.conj y⁻¹) (g : DA Δ) ∈ _ ↔ _
  rw [MulAut.conj_apply, inv_inv]

private theorem conj_at (y g : DA Δ) (v : Pl F) (h : y.1 v = 1) : (y⁻¹ * g * y).1 v = g.1 v := by
  have : (y⁻¹ * g * y).1 v = (y.1 v)⁻¹ * g.1 v * y.1 v := rfl
  rw [this, h, inv_one, one_mul, mul_one]

private theorem up (A A₀ : SD Δ) (hA : A.Ok) (hA₀ : A₀.Ok) (hE : A.Ext A₀) (x : DA Δ) (h0 : x ∈ A₀.dat.U2)
    (hn : ∀ v (h : v ∈ A.Sg), v ∉ A₀.Sg → Sig.eD (A.hs v h) (x.1 v) ∈ (Sig.Lev.iw (Kv v)).J 2) : x ∈ A.dat.U2 := by
  have d0 := ((datOk F Δ A₀ hA₀).2.2.2.2 x).1 h0
  refine ((datOk F Δ A hA).2.2.2.2 x).2 ⟨fun v hv => ?_, fun v hv => d0.2 v fun h => hv (hE.sub h)⟩
  by_cases h : v ∈ A₀.Sg
  · rw [hE.V v h, eD_congr (A.hs v hv) (A₀.hs v h) (hE.s v h)]
    exact d0.1 v h
  · rw [hE.iw v hv h]
    exact hn v hv h

end Gen

section Br
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L}

private theorem spl (hB : B.Ok) (w : Plc L) (R : B.toRingBr.Split w) (g : SA B.Δ)
    (h : cLoc w (B.bS g : UA L 2) ∈ (iw w).J 2) :
    Sig.eD R.hs ((g : DA B.Δ).1 (un w)) ∈ (Sig.Lev.iw (Kv (un w))).J 2 := by
  rw [hB.splS w R g] at h
  exact (R.J (Sig.Lev.iw _) (iw w) rfl (fun a => R.Uo a) 2 _).1 h

private theorem lev_mem {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)} {V : ∀ w : Plc L, Sig.Lev (Kw w)} {x : UA L n}
    (h : x ∈ lev U S V) : x ∈ U ∧ ∀ w ∈ S, cLoc w x ∈ (V w).J n := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
  refine ⟨h1, fun w hw => ?_⟩
  simp only [Subgroup.mem_iInf] at h2
  exact h2 w hw

end Br

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.So.levExt :
    UpperTheory.V.Z.Sym.So.LevExt := by
  intro L _ _ _ B hB T S VL A hA hF A₀ hA₀ hE S₁ h1 _ U y hy hU g hg
  obtain ⟨hgU, hgJ⟩ := lev_mem hg
  refine (mem_lvS A y g).2 (up A A₀ hA hA₀ hE _ ((mem_lvS A₀ y g).1 (hU g hgU)) ?_)
  intro v hv h0
  obtain ⟨w, hwS, rfl⟩ := (hF.sg v).1 hv
  have hsp : IsSplitAt w := hF.pl.split w hwS
  rw [conj_at y (g : DA B.Δ) _ (hy _ hv), eD_congr (A.hs _ hv) (T w hsp).hs (hF.s w hwS hsp)]
  exact spl hB w (T w hsp) g (hgJ w ((h1 w hwS).resolve_right h0))

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TwoUnder
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exSec {W P : Type} {X : P → Type} (f : W → P) (S : Set W) (inj : Set.InjOn f S)
    (g : ∀ w, w ∈ S → X (f w)) (d : ∀ p, X p) : ∃ b : ∀ p, X p, ∀ w (h : w ∈ S), b (f w) = g w h := by
  classical
  refine ⟨fun p => if h : ∃ w, ∃ hw : w ∈ S, f w = p then h.choose_spec.choose_spec ▸ g _ h.choose_spec.choose else d p, ?_⟩
  intro w hw
  have key : ∀ (w' : W) (hw' : w' ∈ S) (he : f w' = f w), (he ▸ g w' hw' : X (f w)) = g w hw := by
    intro w' hw' he
    obtain rfl := inj hw' hw he
    rfl
  have hex : ∃ w', ∃ hw' : w' ∈ S, f w' = f w := ⟨w, hw, rfl⟩
  simp only [dif_pos hex]
  exact key _ _ _

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem exOver (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hne : P ≠ ⊥ := fun h => v.ne_bot (by
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 (Lp L)) (𝓞 L)))
  exact ⟨⟨P, hPm.isPrime, hne⟩, HeightOneSpectrum.ext (by
    rw [HeightOneSpectrum.under_asIdeal]
    exact hP.over.symm)⟩

private theorem exTwo : ∃ w : Plc L, (2 : 𝓞 L) ∈ w.asIdeal := by
  have hu : ¬ IsUnit (2 : 𝓞 L) := fun h => by
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ((u : 𝓞 L) : L) = algebraMap ℚ L (1 / 2) := by
      have e1 : (2 : L) * ((u : 𝓞 L) : L) = 1 := by
        have := congrArg (algebraMap (𝓞 L) L) hu
        rwa [map_mul, map_ofNat, map_one] at this
      rw [map_div₀, map_one, map_ofNat]
      field_simp
      linear_combination e1
    have hi : IsIntegral ℤ (algebraMap ℚ L (1 / 2)) := e ▸ u.2
    have hi' : IsIntegral ℤ (1 / 2 : ℚ) := (isIntegral_algebraMap_iff ).1 hi
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
    have h2 : (2 : ℚ) * (y : ℚ) = 1 := by
      rw [show (y : ℚ) = 1 / 2 from hy]; norm_num
    have h3 : (2 : ℤ) * y = 1 := by exact_mod_cast h2
    omega
  obtain ⟨P, hPm, hP⟩ := exists_max_ideal_of_mem_nonunits hu
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hP
    exact two_ne_zero hP
  exact ⟨⟨P, hPm.isPrime, hne⟩, hP⟩

private theorem two_under (w : Plc L) (h : (2 : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (2 : 𝓞 L) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_ofNat] at h
  exact h

private def pullLev {B : Bridge L} {w : Plc L} (T : B.toRingBr.Split w) (V : Lev (Kw w)) : Lev (Kv (un w)) where
  c := V.c
  H := V.H.comap (Units.map (T.i : Kv (un w) →* Kw w))
  le := fun x hx => V.le ((T.Uc _ x).2 hx)
  H_le := fun x hx => (T.Uo x).1 (V.H_le hx)

theorem UpperTheory.V.Z.Sym.So.fitEx :
    UpperTheory.V.Z.Sym.So.FitEx := by
  classical
  intro L _ _ _ B hB T S VL hP h2
  have hinj : Set.InjOn (fun w : Plc L => un w) (S : Set (Plc L)) := hP.inj
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨sf, hsf⟩ := exSec (X := fun v : Pl (Lp L) => Kv v) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (T w (hP.split w hw)).s) (fun _ => 0)
    obtain ⟨Vf, hVf⟩ := exSec (X := fun v : Pl (Lp L) => Lev (Kv v)) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => pullLev (T w (hP.split w hw)) (VL w)) (fun _ => Lev.iw _)
    obtain ⟨χ, hχ⟩ := hB.chi
    have hs : ∀ v ∈ S.image (fun w : Plc L => un w), sf v * sf v = cv v B.Δ := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      rw [hsf w hw]
      exact (T w (hP.split w hw)).hs
    let A : SD B.Δ :=
      { Sg := S.image (fun w : Plc L => un w)
        s := sf
        hs := hs
        V := Vf
        Ry := fun v => (finFacts _ (Vf v)).2.2.2.2.1.choose
        χ := χ }
    have hoff : ∀ v ∉ A.Sg, (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro v hv h
      obtain ⟨w, rfl⟩ := exOver v
      obtain ⟨w', hw', he⟩ := h2 w (two_under w h)
      exact hv (Finset.mem_image.2 ⟨w', hw', he⟩)
    refine ⟨A, ⟨inferInstance, B.neg, ?_, ?_, ?_, ?_⟩, ⟨hP, ?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨w, hw⟩ := exTwo (L := L)
      obtain ⟨w', hw', -⟩ := h2 w hw
      exact ⟨_, Finset.mem_image_of_mem _ hw'⟩
    · exact fun v hv => B.loc v (hoff v hv)
    · intro v
      by_cases hv : v ∈ A.Sg
      · exact hχ v (Or.inr ⟨sf v, (hs v hv).symm⟩)
      · exact hχ v (Or.inl (hoff v hv))
    · exact fun v _ => (finFacts _ (Vf v)).2.2.2.2.1.choose_spec
    · intro v
      simp [A]
    · intro w hw h
      exact hsf w hw
    · intro w hw
      show (Vf (un w)).c = _
      rw [hVf w hw]; rfl
    · intro w hw h x
      show _ ↔ x ∈ (Vf (un w)).H
      rw [hVf w hw]; rfl
  · obtain ⟨b, hb⟩ := exSec (X := fun v : Pl (Lp L) => (Kv v)ˣ →* ℂˣ) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (a w).comp (iu T w (hP.split w hw))) (fun _ => 1)
    exact ⟨b, fun w hw h => hb w hw⟩

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FitExt
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lev_ext' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V V' : Sig.Lev k} (hc : V.c = V'.c) (hH : V.H = V'.H) : V = V' := by
  cases V
  cases V'
  cases hc
  cases hH
  rfl

theorem UpperTheory.V.Z.Sym.So.fitExt :
    UpperTheory.V.Z.Sym.So.FitExt := by
  intro L _ _ _ B T S₀ S V₀ VL A₀ A h₀ h hS hV hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    exact (h.sg _).2 ⟨w, hS hw, rfl⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    rw [h.s w (hS hw) hs, h₀.s w hw hs]
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    have e : A.V (un w) = A₀.V (un w) :=
      lev_ext' (by rw [h.c w (hS hw), h₀.c w hw, hV w hw]) (by
        ext x
        rw [← h.H w (hS hw) hs x, ← h₀.H w hw hs x, hV w hw])
    rw [e]
  · intro v hv hn
    obtain ⟨w, hw, rfl⟩ := (h.sg v).1 hv
    have hw0 : w ∉ S₀ := fun hw0 => hn ((h₀.sg _).2 ⟨w, hw0, rfl⟩)
    have hs : IsSplitAt w := h.pl.split w (Finset.mem_coe.2 hw)
    have hi := hI w hw hw0
    have e : A.V (un w) = Sig.Lev.iw _ :=
      lev_ext' (by rw [h.c w hw, hi]; rfl) (by
        ext x
        rw [← h.H w hw hs x, hi]
        exact (T w hs).Uo x)
    rw [e]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ThetaTheta
namespace UpperTheory.V.Z.Sym.Glob

open Loc

end UpperTheory.V.Z.Sym.Glob

private theorem theta_apply_eq_star {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (i j : Fin 3) :
    (UpperTheory.V.Z.Sym.Loc.theta Δ g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j = star ((g : Matrix (Fin 3) (Fin 3) (UpperTheory.V.Z.Sym.Lsq K Δ)) i j) := by
  simp [UpperTheory.V.Z.Sym.Loc.theta]

private theorem theta_theta' {K : Type} [Field K] (Δ : K) (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ (UpperTheory.V.Z.Sym.Loc.theta Δ g) = g := by
  apply Subtype.ext
  exact Matrix.ext fun i j => by rw [theta_apply_eq_star, theta_apply_eq_star, star_star]

private theorem theta_mem_ku_of_mem_ku (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] (Δ : K)
    (g : UpperTheory.V.Z.Sym.Loc.U3 Δ) (hg : g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ) :
    UpperTheory.V.Z.Sym.Loc.theta Δ g ∈ UpperTheory.V.Z.Sym.Loc.KU O Δ := by
  intro i j
  rw [theta_apply_eq_star, star_star]
  exact ⟨(hg i j).2, (hg i j).1⟩

private theorem lmap_star_scalar_tuples {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K)
    (x : UpperTheory.V.Z.Sym.Lsq K Δ) :
    UpperTheory.V.Z.Sym.Glob.lmap f Δ (star x) = star (UpperTheory.V.Z.Sym.Glob.lmap f Δ x) := by
  ext <;> simp [UpperTheory.V.Z.Sym.Glob.lmap]

open UpperTheory.V.Z.Sym.Loc in
theorem UpperTheory.V.Z.Sym.Glob.baseG :
    UpperTheory.V.Z.Sym.Glob.BaseG := by
  intro F _ _ Δ D _ V _ _ W Θ ch hΘ htr
  obtain ⟨⟨ι, hι⟩, -, -⟩ := UpperTheory.V.Z.Sym.Glob.iotaEx F Δ
  let tΓ : UpperTheory.V.Z.Sym.Loc.U3 Δ ≃* UpperTheory.V.Z.Sym.Loc.U3 Δ :=
    MonoidHom.toMulEquiv (UpperTheory.V.Z.Sym.Loc.theta Δ) (UpperTheory.V.Z.Sym.Loc.theta Δ)
      (by ext1 g; exact theta_theta' Δ g) (by ext1 g; exact theta_theta' Δ g)
  let tG0 : UpperTheory.V.Z.Sym.Glob.GA Δ →* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    { toFun := fun g => ⟨fun v => UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) (g.1 v),
        Filter.Eventually.mono (show ∀ᶠ v in Filter.cofinite, g.1 v ∈ UpperTheory.V.Z.Sym.Loc.KU
          (UpperTheory.V.Z.Sym.Glob.Ov v) (UpperTheory.V.Z.Sym.Glob.cv v Δ) from g.2)
          fun v hv => theta_mem_ku_of_mem_ku _ _ _ hv⟩
      map_one' := Subtype.ext (funext fun v => map_one _)
      map_mul' := fun a b => Subtype.ext (funext fun v => map_mul _ _ _) }
  let tG : UpperTheory.V.Z.Sym.Glob.GA Δ ≃* UpperTheory.V.Z.Sym.Glob.GA Δ :=
    MonoidHom.toMulEquiv tG0 tG0
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
      (by ext1 g; exact Subtype.ext (funext fun v => theta_theta' _ _))
  let B : UpperTheory.V.Z.Sym.Base (UpperTheory.V.Z.Sym.Loc.U3 Δ) (UpperTheory.V.Z.Sym.Glob.GA Δ) V :=
    { ι := ι, U := D.UG, ω := 1, W := W, Γ₀ := ⊥
      cenΓ := bot_le
      cenG := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      memU := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz, map_one]
        exact one_mem _
      scal := by
        intro z hz v
        obtain rfl := Subgroup.mem_bot.mp hz
        rw [MonoidHom.one_apply, Units.val_one, one_smul, map_one]
        rfl }
  let s : B.Tw :=
    { θΓ := tΓ, θ := tG, Θ := Θ
      comm := by
        intro γ
        apply Subtype.ext
        funext v
        apply Subtype.ext
        show ((UpperTheory.V.Z.Sym.Loc.theta (UpperTheory.V.Z.Sym.Glob.cv v Δ) ((ι γ).1 v)).1) =
          ((ι (UpperTheory.V.Z.Sym.Loc.theta Δ γ)).1 v).1
        rw [hι (UpperTheory.V.Z.Sym.Loc.theta Δ γ) v]
        refine Matrix.ext fun i j => ?_
        rw [theta_apply_eq_star, hι γ v, Matrix.map_apply, Matrix.map_apply, theta_apply_eq_star, lmap_star_scalar_tuples]
      int := hΘ
      fix := by
        intro z hz
        rw [Subgroup.mem_bot.mp hz]
        exact map_one _ }
  exact ⟨B, s, ⟨hι, rfl, rfl, rfl, fun γ => rfl, fun g v => rfl, htr⟩, rfl, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.LevUnion
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_prd (L : Type) [Field L] [NumberField L] [IsCMField L] (z : Lp L) :
    ∏ w : InfinitePlace L, w.embedding (algebraMap (Lp L) L z) = ((Algebra.norm ℚ z : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ z
  rw [eq_ratCast] at h
  rw [h]
  have hr : ∀ (τ : L →+* ℂ) (x : Lp L), (InfinitePlace.mk τ).embedding (algebraMap (Lp L) L x) = τ (algebraMap (Lp L) L x) := by
    intro τ x
    rcases InfinitePlace.embedding_mk_eq τ with e | e <;> rw [e]
    exact x.2 τ
  refine Finset.prod_bij (fun w _ => (w.embedding.comp (algebraMap (Lp L) L)).toRatAlgHom) (fun _ _ => Finset.mem_univ _)
    (fun w _ w' _ e => ?_) (fun σ _ => ⟨InfinitePlace.mk (ComplexEmbedding.lift L σ.toRingHom), Finset.mem_univ _, ?_⟩) fun _ _ => rfl
  · have e' : w.embedding.comp (algebraMap (Lp L) L) = w'.embedding.comp (algebraMap (Lp L) L) := RingHom.ext fun x => AlgHom.congr_fun e x
    apply (IsCMField.equivInfinitePlace L).injective
    change w.comap (algebraMap (Lp L) L) = w'.comap (algebraMap (Lp L) L)
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk, e']
  · ext x
    exact (hr _ _).trans (ComplexEmbedding.lift_algebraMap_apply L _ x)

private theorem lev_union {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (U : Subgroup (UA L n)) (S₀ S₁ S : Finset (Plc L))
    (V₀ V₁ V : ∀ w : Plc L, Lev (Kw w)) (hS : ∀ w, w ∈ S ↔ w ∈ S₀ ∨ w ∈ S₁) (h0 : ∀ w ∈ S₀, V w = V₀ w) (h1 : ∀ w ∈ S₁, V w = V₁ w) :
    lev (lev U S₀ V₀) S₁ V₁ = lev U S V := by
  ext x
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h => ⟨h.1.1, fun w hw => ((hS w).1 hw).elim (fun a => h0 w a ▸ h.1.2 w a) fun a => h1 w a ▸ h.2 w a⟩,
    fun h => ⟨⟨h.1, fun w a => h0 w a ▸ h.2 w ((hS w).2 (.inl a))⟩, fun w a => h1 w a ▸ h.2 w ((hS w).2 (.inr a))⟩⟩

private theorem iota_eq {F : Type} [Field F] [NumberField F] {Δ : F} {ι ι' : DX Δ →* DA Δ} (h : IsIotaD ι) (h' : IsIotaD ι') : ι = ι' :=
  MonoidHom.ext fun γ => Subtype.ext (funext fun v => Subtype.ext (Units.ext ((h γ v).trans (h' γ v).symm)))

section

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem bG (hD : D.Ok) (W : Representation ℂ (U3 Δ) V) (Θ : V →ₗ[ℂ] V) (ch : F → ℂ) (h1 : ∀ γ v, Θ (W γ v) = W (theta Δ γ) (Θ v))
    (h2 : ∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (W δ ∘ₗ Θ) = ch τ) :
    ∃ (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s ∧ B.W = W ∧ s.Θ = Θ := baseG F Δ D hD V W Θ ch h1 h2

private theorem bS (hD : D.Ok) (W : Representation ℂ (SU Δ) V) (ch : F → ℂ)
    (h : ∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (W γ) = ch τ) (x : DA Δ) :
    ∃ B : Base (SU Δ) (SA Δ) V, D.IsBS ch x B ∧ B.W = W := baseS F Δ D hD V W ch h x

private theorem bK (hD : D.Ok) (W : Representation ℂ (DX Δ) V) (ch : F → ℂ)
    (h1 : ∀ z s, IsScal z s → ∀ v, W s v = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ • v)
    (h2 : ∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) → LinearMap.trace ℂ V (W g) = ch τ) :
    ∃ B : Base (DX Δ) (DA Δ) V, D.IsBK ch B ∧ B.W = W := baseK F Δ D hD V W ch h1 h2

private theorem iK {ch : F → ℂ} {B : Base (DX Δ) (DA Δ) V} (h : D.IsBK ch B) : IsIotaD B.ι := h.ι

end

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L)

private theorem baseK' (A : SD B.Δ) (hA : A.Ok) {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1)), A.dat.IsBK (Wt.ch (em B) j) C ∧ C.W = Wt.cK (em B) j :=
  bK A.dat (datOk _ _ A hA).1 (Wt.cK (em B) j) (Wt.ch (em B) j) (fun z s h v => by
    rw [Wt.cK_scal _ hj z s h v, ← norm_prd L]
    congr 2
    exact Finset.prod_congr rfl fun w _ => congrArg w.embedding (B.e_alg _)) (Wt.cK_tr _ hj)

private theorem fitSq (T : Spl B) (S : Finset (Plc L)) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b) :
    FitCh T S (fun w => a w ^ 2) (b ^ 2) := fun w hw h => by
  rw [Pi.pow_apply, hb w hw h]
  ext z
  simp

private theorem core (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (V : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (f : Fit T S V A)
    {j : ℕ} (hj : 1 ≤ j) (e : InfinitePlace L → ℤ) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b)
    (φ : UA L 2 → Wt.VD (InfinitePlace L) j) (h0 : φ ≠ 0) (hφ : IsAF (repE j e) (lev (Kall L 2) S V) φ) (E : ∀ w ∈ S, EigS φ w (V w) (a w))
    (BK : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1))) (hK : A.dat.IsBK (Wt.ch (em B) j) BK) :
    (∃ φ : UA L 3 → Wt.VG (InfinitePlace L) j, φ ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (Kall L 3) S V) φ ∧
      ∀ w ∈ S, EigT φ w (V w) ![a w, 1, (a w)⁻¹]) ∨ ∃ φ' ∈ BK.Forms, φ' ≠ 0 ∧ A.EigK φ' (b ^ 2) := by
  classical
  haveI : ∀ (K : Type) [Fintype K] (d : ℕ) (n : K → ℕ), FiniteDimensional ℂ (Wt.MH d n) := Wt.finMH
  have hD := (datOk _ _ A hA).1
  refine (inS L B hB T S V A hA f j e a b hb φ h0 hφ E).elim fun y Hy => ?_
  refine (bG A.dat hD (Wt.cG (em B) j) (Wt.thG _ j) (Wt.ch (em B) j) (Wt.cG_int _ hj) (Wt.cG_tr _ hj)).elim fun BG h =>
    h.elim fun s hG => ?_
  refine (bS A.dat hD (Wt.cS (em B) j) (Wt.ch (em B) j) (Wt.cS_tr _ hj) y).elim fun BS hS => ?_
  refine (Hy.2 _ BS hS.1 hS.2).elim fun ψ p => ?_
  refine (specF _ _ A hA _ _ _ _ BG s y BS BK hG.1 Hy.1 hS.1 hK b ψ p.1 p.2.1 p.2.2).imp_left fun q => q.elim fun φ' q => ?_
  exact outG L B hB T S V A hA f j a b hb _ BG s hG.1 hG.2.1 φ' q.1 q.2.1 q.2.2

private theorem second (hB : B.Ok) (T : Spl B) (S S₁ : Finset (Plc L)) (V : ∀ w : Plc L, Lev (Kw w)) (A A₀ : SD B.Δ) (hA : A.Ok) (hA₀ : A₀.Ok)
    (f : Fit T S V A) (hx : A.Ext A₀) (hS : ∀ w ∈ S, w ∈ S₁ ∨ un w ∈ A₀.Sg) (hs1 : S₁ ⊆ S) (v1 : ∀ w ∈ S₁, V w = iw w)
    (m : ℕ) (U : Subgroup (UA L 2)) (hm : 3 ≤ m) (u1 : IsCong m U) (hf : Full U S₁) {j : ℕ}
    (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b)
    (BK : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1))) (hK : A.dat.IsBK (Wt.ch (em B) j) BK) (k1 : BK.W = Wt.cK (em B) j)
    (Y : Finset (DA B.Δ)) (hY : A₀.Reps BK.ι Y) (hoff : ∀ y ∈ Y, A.dat.Off y)
    (m2 : ∀ y ∈ Y, ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ U → g ∈ A₀.lvS y)
    (φ' : DA B.Δ → Wt.VD (InfinitePlace L) (2 * j + 1)) (q1 : φ' ∈ BK.Forms) (q2 : φ' ≠ 0) (q3 : A.EigK φ' b) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) (2 * j + 1), φ ≠ 0 ∧ IsAF (repE (2 * j + 1) 0) (lev U S₁ iw) φ ∧ ∀ w ∈ S₁, EigS φ w (iw w) (a w) := by
  refine (kNon _ _ A hA A₀ hA₀ hx _ _ BK hK Y hY hoff φ' q1 q2).elim fun x h => h.2.elim fun t ht => ?_
  have sf := kRes _ _ A hA _ _ BK hK x (hoff x h.1) φ' q1 _ q3
  rw [k1] at sf
  have hl := levExt L B hB T S V A hA f A₀ hA₀ hx S₁ hS (fun w hw => ⟨hs1 hw, v1 w hw⟩) U x (hoff x h.1) (m2 x h.1)
  have hn : (fun g : SA B.Δ => φ' (g * x)) ≠ 0 := fun h => ht (congrFun h t)
  have ho := outS L B hB T S V A hA f S₁ hs1 v1 m U hm u1 hf (2 * j + 1) (-((j : ℤ) + 1)) a b hb _ (iK _ hK) x (hoff x h.1) hl _ hn
  exact ho sf

private theorem offAll (T : Spl B) (S S₀ S₁ : Finset (Plc L)) (V V₀ : ∀ w : Plc L, Lev (Kw w)) (A A₀ : SD B.Δ) (f : Fit T S V A) (f₀ : Fit T S₀ V₀ A₀)
    (hS : ∀ w, w ∈ S ↔ w ∈ S₀ ∨ w ∈ S₁) (y : DA B.Δ) (h0 : A₀.dat.Off y) (h1 : ∀ w ∈ S₁, y.1 (un w) = 1) : A.dat.Off y := fun v hv =>
  ((f.sg v).1 hv).elim fun w hw => hw.2 ▸ ((hS w).1 hw.1).elim (fun h => h0 _ ((f₀.sg _).2 ⟨w, h, rfl⟩)) (h1 w)

end

def UpperTheory.V.Z.Sym.W.SpecOutS : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ S₀ : Finset (Plc L), Places (S₀ : Set (Plc L)) → HasTwo S₀ →
    ∀ j : ℕ, 1 ≤ j → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ U₂ : Subgroup (UA L 2), IsLevel U₂ ∧
    ∀ S₁ : Finset (Plc L), Disjoint S₀ S₁ → Places ((S₀ : Set (Plc L)) ∪ S₁) → (∀ w ∈ S₁, locU 2 w ⊓ Kall L 2 ≤ U₂) →
    ∀ (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 →
      IsAF (repE j e) (lev (lev (Kall L 2) S₀ (deep c)) S₁ iw) φ →
      (∀ w ∈ S₀, EigS φ w (deep c w) (a w)) → (∀ w ∈ S₁, EigS φ w (iw w) (a w)) →
      (∃ φ' : UA L 3 → Wt.VG (InfinitePlace L) j, φ' ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (lev (Kall L 3) S₀ (deep c)) S₁ iw) φ' ∧
        (∀ w ∈ S₀, EigT φ' w (deep c w) ![a w, 1, (a w)⁻¹]) ∧ ∀ w ∈ S₁, EigT φ' w (iw w) ![a w, 1, (a w)⁻¹]) ∨
      ∃ φ' : UA L 2 → Wt.VD (InfinitePlace L) (2 * j + 1), φ' ≠ 0 ∧ IsAF (repE (2 * j + 1) 0) (lev U₂ S₁ iw) φ' ∧
        ∀ w ∈ S₁, EigS φ' w (iw w) (a w ^ 2)

theorem UpperTheory.V.Z.Sym.W.specOutS : UpperTheory.V.Z.Sym.W.SpecOutS := by
  classical
  intro L _ _ _ hU S₀ hP hT j hj
  refine (bridgeEx L hU).elim fun B hB => ?_
  have T : Spl B := fun w h => (hB.split w h).some
  refine ⟨0, fun c _ => ?_⟩
  refine (fitEx L B hB T S₀ (deep c) hP hT).1.elim fun A₀ h₀ => ?_
  refine (iotaEx (Lp L) B.Δ).2.1.elim fun ι hι => ?_
  refine (repsEx _ _ A₀ h₀.1 classRep ι hι).elim fun Y hY => ?_
  refine (congLev L B hB T S₀ (deep c) A₀ h₀.1 h₀.2 Y fun y hy => (hY.1 y hy).2).elim fun m hm => ?_
  refine (congEx L 2 m (by have := hm.1; omega)).elim fun U u => ?_
  refine ⟨U, u.2.1, fun S₁ hd hP' hf a e φ h0 hφ E0 E1 => ?_⟩
  have hS : ∀ w, w ∈ S₀ ∪ S₁ ↔ w ∈ S₀ ∨ w ∈ S₁ := fun _ => Finset.mem_union
  have hPS : Places ((S₀ ∪ S₁ : Finset (Plc L)) : Set (Plc L)) := by rwa [Finset.coe_union]
  generalize S₀ ∪ S₁ = S at hS hPS
  have hV : ∃ V : ∀ w : Plc L, Lev (Kw w), (∀ w ∈ S₀, V w = deep c w) ∧ ∀ w ∈ S₁, V w = iw w :=
    ⟨fun w => if w ∈ S₁ then iw w else deep c w, fun w hw => if_neg (Finset.disjoint_left.1 hd hw), fun w hw => if_pos hw⟩
  refine hV.elim fun V v => ?_
  have hF := fitEx L B hB T S V hPS fun w hw => (hT w hw).imp fun w' h => ⟨(hS w').2 (.inl h.1), h.2⟩
  refine hF.1.elim fun A hA => (hF.2 a).elim fun b hb => ?_
  have hs0 : S₀ ⊆ S := fun w hw => (hS w).2 (.inl hw)
  have hs1 : S₁ ⊆ S := fun w hw => (hS w).2 (.inr hw)
  have hx : A.Ext A₀ := fitExt L B T S₀ S (deep c) V A₀ A h₀.2 hA.2 hs0 v.1 fun w hw h => v.2 w (((hS w).1 hw).resolve_left h)
  rw [lev_union _ S₀ S₁ S _ _ V hS v.1 v.2] at hφ
  rw [lev_union _ S₀ S₁ S _ _ V hS v.1 v.2]
  refine (baseK' B A hA.1 hj).elim fun BK hK => ?_
  have eι : ι = BK.ι := iota_eq hι (iK _ hK.1)
  refine (core B hB T S V A hA.1 hA.2 hj e a b hb φ h0 hφ (fun w hw =>
    ((hS w).1 hw).elim (fun h => v.1 w h ▸ E0 w h) fun h => v.2 w h ▸ E1 w h) BK hK.1).imp
    (fun r => r.imp fun r h => ⟨h.1, h.2.1, fun w hw => v.1 w hw ▸ h.2.2 w (hs0 hw), fun w hw => v.2 w hw ▸ h.2.2 w (hs1 hw)⟩) fun q => q.elim fun φ' q => ?_
  exact second B hB T S S₁ V A A₀ hA.1 h₀.1 hA.2 hx (fun w hw => ((hS w).1 hw).elim (fun h => .inr ((h₀.2.sg _).2 ⟨w, h, rfl⟩)) .inl) hs1 v.2
    m U hm.1 u.1 ⟨u.2.1.1, hf⟩ _ _ (fitSq B T S a b hb) BK hK.1 hK.2 Y (eι ▸ hY)
    (fun y hy => offAll B T S S₀ S₁ V _ A A₀ hA.2 h₀.2 hS y (hY.1 y hy).1 fun w hw =>
      hm.2.1 w (u.2.2 le_rfl w (hPS.split w (hs1 hw)) (hf w hw)) y hy)
    (hm.2.2 U u.1) φ' q.1 q.2.1 q.2.2

end
end

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al


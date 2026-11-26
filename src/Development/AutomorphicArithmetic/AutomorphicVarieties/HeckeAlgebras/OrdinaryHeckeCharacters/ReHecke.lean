module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.MemOrdC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ReHecke
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem re_chi {n : ℕ} {k H : Type} [CommRing k] [Group H] (χ : Fin n → H →* kˣ) (g : H) :
    (W.GDet.ofRep (W.diagRep χ)).chi (MonoidAlgebra.single g 1) = ∏ i, (X - C (χ i g : k)) := by
  change (W.GDet.repAlg (W.diagRep χ) k[X] _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, W.diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

private theorem re_hecke {k : Type} [Field k] {n q : ℕ} (hq : (q : k) ≠ 0) (P : k[X]) (hm : P.Monic)
    (hn : P.natDegree = n) : ∃ b : Fin n → k,
      P = heckePol n q fun j => if h : 0 < j ∧ j - 1 < n then b ⟨j - 1, h.2⟩ else 1 := by
  refine ⟨fun i => (-1) ^ (i + 1 : ℕ) * ((q : k) ^ ((i + 1) * i / 2 : ℕ))⁻¹ * P.coeff (n - (i + 1)), ?_⟩
  rw [Hi.heckePol, ← Finset.sum_range_reflect]
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow, hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  rw [show j + d + 1 - 1 - j = d by omega, show j + d - d = j by omega]
  congr 2
  rcases d with _ | d
  · have := hm.coeff_natDegree
    rw [hn] at this
    simpa using this
  · rw [dite_eq_left ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel]
    have h1 : ((-1 : k) ^ (d + 1)) * (-1) ^ (d + 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq)
    linear_combination (-P.coeff j) * h2 - P.coeff j * ((q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹) * h1

open scoped Pointwise in
private theorem re_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (χ : G E Ω →* M) {w : HeightOneSpectrum (𝓞 E)}
    (hχ : ∀ A, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, χ s = 1) {q : ℕ} {A B : ValuationSubring Ω}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) {σ τ : G E Ω} (hσ : IsFrob A q σ) (hτ : IsFrob B q τ) :
    χ τ = χ σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hB
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  have h0 : IsFrob (F := E) A q (g⁻¹ * τ * g) := by
    refine ⟨?_, fun x hx => ?_⟩
    · have h1 : τ • g • A = g • A := hτ.1
      show (g⁻¹ * τ * g) • A = A
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · have h1 := hτ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
        ← ValuationSubring.valuation_le_one_iff])
      have e : τ (g x) - g x ^ q = g ((g⁻¹ * τ * g) x - x ^ q) := by
        rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
      rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
        ← valuation_lt_one_iff'] at h1
  have h2 := hχ A hA _ (inv_mul_mem_Ine_of_isFrob hσ h0)
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at h2
  exact h2.symm

private theorem re_art {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {M : Type} [CommGroup M]
    (ψ : Dec (F := E) A →* M) (hψ : IsOpen (ψ.ker : Set (Dec (F := E) A))) {x y : Weil h} (hxy : a x = a y) :
    ψ (Subgroup.inclusion (Weil_le_Dec h) x) = ψ (Subgroup.inclusion (Weil_le_Dec h) y) := by
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : Finite (Dec (F := E) A ⧸ ψ.ker) := ψ.ker.quotient_finite_of_isOpen hψ
  haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  let ι := Subgroup.inclusion (Weil_le_Dec h)
  by_contra hne
  have h1 : ψ.rangeRestrict (ι (x * y⁻¹)) ≠ 1 := fun h1 => hne (by
    have h2 : ψ (ι (x * y⁻¹)) = 1 := congrArg Subtype.val h1
    rwa [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h2)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ψ.range ℂ h1
  have hs : GlobalTheory.WeilDeligne.IsSmooth (ψ.comp ι) :=
    hψ.preimage (f := Subgroup.inclusion (Ine_le_Dec (F := E) A)) (continuous_inclusion (Ine_le_Dec (F := E) A))
  obtain ⟨χ, -, hχ⟩ := ha.factor (φ.comp (ψ.rangeRestrict.comp ι)) (hs.of_le fun σ hσ => by
    have : ψ.rangeRestrict (ι σ) = 1 := Subtype.ext hσ
    simp only [MonoidHom.comp_apply, this, map_one])
  apply hφ
  have h3 := DFunLike.congr_fun hχ (x * y⁻¹)
  rw [MonoidHom.comp_apply χ, map_mul a, map_inv a, hxy, mul_inv_cancel, map_one] at h3
  exact h3

private theorem re_eps {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ε : H →* ℤ_[l]ˣ) (hε : Continuous ε) :
    IsOpen (((Units.map ((algebraMap c.O (ResidueField c.O)).comp (algebraMap ℤ_[l] c.O)).toMonoidHom).comp ε).ker : Set H) := by
  haveI : FaithfulSMul ℤ_[l] c.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h1 : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y] at h1
    exact Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h1)
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := inferInstance
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ := by fun_prop
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset ((isOpen_lt hc continuous_const (g := fun _ => 1)).mem_nhds (by simp)) fun g hg => ?_)
  have h1 : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := PadicInt.mem_nonunits.2 hg
  have h2 := (residue_eq_zero_iff _).2 (map_nonunit (algebraMap ℤ_[l] c.O) _ h1)
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
  exact Units.ext h2

theorem UpperTheory.V.Hi.resEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ r : Resid V.frame c.O n, ∃ a, IsRes Q r τ₀ a := by
  intro hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r
  have H1 : ∀ w : (hset Q τ₀).Wp, ∃ b : Fin n → c.O, ∀ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 →
      IsFrob B (normV w.1) σ → r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) =
      heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (b ⟨j - 1, h.2⟩) else 1 := by
    rintro ⟨w, hw, -⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun hl => hw (V.sub (Or.inl (by
      change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
      rwa [map_natCast])))
    have hq : ((normV w : ℕ) : ResidueField c.O) ≠ 0 := by
      have h1 := (cycZ L Ω l φ).isUnit.map ((residue c.O).comp (algebraMap ℤ_[l] c.O))
      rw [cycZ_of_isFrob hl hA hφ, map_natCast] at h1
      exact h1.ne_zero
    have hI : ∀ B, IsPlaceOver B w → ∀ t ∈ Ine (F := L) B, V.pr t = 1 := fun B hB t ht => by
      refine Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_)
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      refine ⟨w.under (𝓞 (Lp L)), hw, B, fun x => ?_, ht.1, ht.2⟩
      rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact hB (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    obtain ⟨b, hb⟩ := re_hecke (n := n) hq (∏ i, (X - C (r.chib i (V.pr φ⁻¹) : ResidueField c.O)))
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
      (by rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp)
    choose b' hb' using fun i => residue_surjective (b i)
    refine ⟨b', fun B σ hB hσ => ?_⟩
    simp only [hb']
    rw [← hb]
    refine (re_chi r.chib (V.pr σ⁻¹)).trans (Finset.prod_congr rfl fun i _ => ?_)
    have := re_frob ((r.chib i).comp V.pr) (fun B hB t ht =>
      (congrArg (r.chib i) (hI B hB t ht)).trans (map_one _)) hA hB hφ hσ
    rw [← inv_inj, ← map_inv, ← map_inv] at this
    exact congrArg (fun u : (ResidueField c.O)ˣ => X - C (u : ResidueField c.O)) this
  have H2 : ∀ (v : V.frame.Vl) (j : Fin n), ∃ b : c.O, ∀ (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)),
      (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) :
        ResidueField c.O) = residue c.O b := by
    intro v j
    have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := Classical.epsilon_spec (UpperTheory.V.Loc.localArtinReciprocity hN (s.hw v.1))
    obtain ⟨y, hy⟩ := ha.surj (unif _)
    obtain ⟨b, hb⟩ := residue_surjective (R := c.O) ((∏ i with i ≤ j,
      r.psib v i (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) *
      (hset Q τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) ^ (i : ℕ) :
        (ResidueField c.O)ˣ) : ResidueField c.O)
    refine ⟨b, fun x g hg hx => ?_⟩
    obtain rfl : g = Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) x := Subtype.ext hg
    rw [hb]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e1 := re_art ha (r.psib v i) (r.psib_open v i) (hx.trans hy.symm)
    have e2 := re_art ha ((hset Q τ₀).epsV (ResidueField c.O) v)
      (re_eps c ((cycZ L Ω l).comp (Dec (F := L) (s.A v.1)).subtype)
        ((continuous_cycZ L Ω l).comp continuous_subtype_val)) (hx.trans hy.symm)
    exact congrArg₂ (fun u t : (ResidueField c.O)ˣ => u * t ^ (i : ℕ)) e1 e2
  choose b1 hb1 using H1
  choose b2 hb2 using H2
  exact ⟨Sum.elim (fun x => b1 x.1 x.2) (fun x => b2 x.1 x.2), ⟨hb1, hb2⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreUp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)

private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]

private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]

private theorem up_vec (hL : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.Part ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := ordA hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩

private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)

end

theorem UpperTheory.V.Hi.coreUp :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.Part ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
end

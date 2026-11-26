module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.CRealAv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrSeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedEndE
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwoRuns
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrLinkedEnd
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
theorem modularity_linked_ends (hMod : _root_.UpperTheory.V.W.ModUAlt) (hLam : W.LamEx)
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
    {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (hL : W.Large L c₁)
    (hs : ∀ J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J) :
    ∃ J : Ideal R.T.B.B, R.T.ModIn J ∧ R.B₀.arithmeticPointClassicalityDense ι J := by
  obtain ⟨hd, hμ⟩ := degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  obtain ⟨Λ, hΛ⟩ := hLam l L Ω R.s R.V c₁ n R.r
  have hn : 1 ≤ n := by rcases R.n23 with h | h <;> omega
  obtain ⟨J, hJ⟩ := hMod l L Ω R.s R.V R.hV hμ c₁ hL n hn R.r R.B₀ Λ ι
  refine ⟨J, ⟨⟨Λ, hJ.ring.fin⟩, ?_, fun g hg => (hJ.ring.unr0 R.v0 g hg).1,
    n4Of Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R, hJ.p1, hJ.p3, hs J hJ.pt⟩, hJ.end2⟩
  intro Z hZ
  haveI : IsDiscreteValuationRing c₁.O := c₁.dvr
  have := dimOf c₁.O Λ.Λ R.B₀.B (Λ.toPair R.B₀.u : Λ.Λ →+* R.B₀.B) J _ hΛ hJ.ring.fin hJ.ring.tf Z hZ
  rw [← hd] at this
  exact this
end UpperTheory.V.Pr
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
def UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (u : W.Plc (W.Lp L))
    (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN u ι (tw r ka)
theorem UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt :
    GlobalTheory.Published.GlobalArtinReciprocity →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ J, R.T.GoodPt J → R.B₀.arithmeticPointClassicalityDense ι J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R.s.v0 k n ι ka := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f n ka R hka J hJ hE A _ _ _ ρ hρ hψ r hr hirr
  have exists_coef : ∃ c₂ : Coef l, c₁.O ≤ c₂.O ∧ ∀ x ∈ A, x ∈ c₂.O := by
    have finite_field {S : Type} [CommRing S] [Algebra ℤ_[l] S] [Module.Finite ℤ_[l] S]
        (φ : S →ₐ[ℤ_[l]] PadicAlgCl l) :
        ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
          ∀ x, φ x ∈ E ∧ ‖φ x‖ ≤ 1 := by
      obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := S)
      have := (s.finite_toSet.image φ).to_subtype
      refine ⟨IntermediateField.adjoin ℚ_[l] (φ '' (s : Set S)),
        IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
        fun x => ⟨?_, ?_⟩⟩
      · have hx : x ∈ Submodule.span ℤ_[l] (s : Set S) := hs ▸ Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul a b _ hb =>
          rw [map_smul, ← algebraMap_smul ℚ_[l] a]
          exact IntermediateField.smul_mem _ hb
      · have hint := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ
        have hi : IsIntegral ℚ_[l] (φ x) := Algebra.IsIntegral.isIntegral _
        change spectralValue (minpoly ℚ_[l] (φ x)) ≤ 1
        rw [spectralValue_le_one_iff (minpoly.monic hi)]
        intro n
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hint, Polynomial.coeff_map]
        exact PadicInt.norm_le_one _
    have : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
    obtain ⟨E₁, f₁, m₁⟩ := finite_field c₁.O.val
    obtain ⟨E₂, f₂, m₂⟩ := finite_field (A.val.restrictScalars ℤ_[l])
    obtain ⟨c₂, hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
    exact ⟨c₂,
      fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩,
      fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩
  obtain ⟨c₂, h₁, h₂⟩ := exists_coef
  let : Algebra c₁.O c₂.O := (Subalgebra.inclusion h₁).toRingHom.toAlgebra
  let φ : A →+* c₂.O := A.val.toRingHom.codRestrict c₂.O fun x => h₂ x.1 x.2
  have isLocal {S : Type} [CommRing S] [Algebra ℤ_[l] S] (f : S →+* c₂.O)
      (hf : ∀ a, f (algebraMap ℤ_[l] S a) = algebraMap ℤ_[l] c₂.O a)
      (hinj : Function.Injective f) : IsLocalHom f := by
    have hint : f.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] S) f ?_
      rw [show f.comp (algebraMap ℤ_[l] S) = algebraMap ℤ_[l] c₂.O from RingHom.ext hf]
      exact fun x => Algebra.IsIntegral.isIntegral x
    exact hint.isLocalHom hinj
  have : IsLocalHom φ := isLocal φ (fun _ => rfl) fun _ _ h =>
    Subtype.ext (congrArg (fun x : c₂.O => x.1) h)
  have hl : IsLocalHom (algebraMap c₁.O c₂.O) := isLocal _ (fun _ => rfl) (Subalgebra.inclusion_injective h₁)
  obtain ⟨hc, hf, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c₂.O
  have : IsCD c₁.O c₂.O := { complete := hc, isLocalHom := hl, fin := hf }
  let j : c₂.O →ₐ[c₁.O] Qbar l := { c₂.O.val.toRingHom with commutes' := fun _ => rfl }
  let ρmap := ρ.map φ
  let ρ₂ : Fr.NRep (Φ.ext f) n c₂.O := ⟨ρmap.r, ρmap.ψ, ρmap.pol, ρmap.diag, ρmap.ord⟩
  have hlift : IsLiftA c₁.O ρ₂ := by
    have residue_eq (x : A) (y : ResidueField c.O)
        (h : residue A x = ResidueField.map (algebraMap c.O A) y) :
        residue c₂.O (φ x) = ResidueField.map (algebraMap c₁.O c₂.O) (f y) := by
      obtain ⟨a, rfl⟩ := residue_surjective y
      rw [R.hf a ⟨a.1, R.le a.2⟩ rfl, ResidueField.map_residue,
        ← ResidueField.map_residue φ, h, ResidueField.map_residue, ResidueField.map_residue]
      rfl
    have map_unit_pow (u : (ResidueField c.O)ˣ) (m : ℤ) :
        f (u ^ m).val = (Units.map f.toMonoidHom u ^ m).val := by
      rw [← map_zpow]; rfl
    have adic_cont {Γ : Type} [TopologicalSpace Γ] {g : Γ → A} (h : Alg.AdicCont (maximalIdeal A) g) :
        Alg.AdicCont (maximalIdeal c₂.O) (fun s => φ (g s)) := fun N => by
      have hle : maximalIdeal A ^ N ≤ (maximalIdeal c₂.O ^ N).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit φ x hx)) N
      exact (h N).comp (Ideal.quotientMap _ φ hle)
    refine ⟨⟨fun i j => adic_cont (hρ.cont.1 i j), fun v i => adic_cont (hρ.cont.2 v i)⟩,
      ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
    · exact (residue_eq _ _ (hρ.bar.1 g i)).trans (congrArg _ (map_unit_pow _ _))
    · exact (residue_eq _ _ (hρ.bar.2 v i g)).trans (congrArg _ (map_unit_pow _ _))
    · have h := residue_eq (ρ.r g i j) 0 ((hρ.diag g i j hij).trans (map_zero _).symm)
      rwa [map_zero, map_zero] at h
  obtain ⟨F, hF, hD, hP⟩ := hJ c₂.O ρ₂ hlift (Qbar l) j Subtype.val_injective fun U hU =>
    hirr.2.2 U le_top fun s v hv => by rw [hr]; exact hU (k.p0 s) trivial v hv
  have hw : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (R.s.w v).asIdeal := fun v => by
    have h1 := (R.s.hA v (l : ℕ)).2 v.2
    refine (R.s.hw v (l : ℕ)).1 ?_
    simpa using h1
  have exists_weights (v : W.Vl l L) :
      ∃ wt : W.Emb l (R.s.w v) → ℤ,
        ∀ (m : ℤ) (χ : G L Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G L Ω)) →
          ∀ κ : Dec (F := L) (R.s.A v) →* (Qbar l)ˣ,
            (∀ g : Dec (F := L) (R.s.A v), (g : G L Ω) ∈ Ine (F := L) (R.s.A v) →
              κ g = cycBar L Ω l g ^ m * χ g * ka g) →
            W.IsLocAlg (R.s.hw v) κ fun τ => wt τ - m := by
    have h := R.s.hw v
    obtain ⟨-, art, Y, a, hart, -, hY⟩ := hka.alg
    refine ⟨fun τ => -a ((ι.toRingHom.comp τ.1).comp (algebraMap L ((R.s.w v).adicCompletion L))),
      fun m χ hχ κ hκ => ?_⟩
    by_cases hl : ∃ b, GlobalTheory.LocLanglands.IsLocalArtin h b
    swap
    · exact ⟨1, by simp, fun b hb => absurd ⟨b, hb⟩ hl⟩
    obtain ⟨ph, h1⟩ := Loc.laHecke h art hart ι Y a ka hY hl
    have h2 := (Loc.laMul h).2.1 _ _ _ m (Loc.laCyc hG h (hw v))
    have h3 := (Loc.laMul h).2.2 (χ.comp (Dec (F := L) (R.s.A v)).subtype)
      (χ.comp (Ine (F := L) (R.s.A v)).subtype)⁻¹
      (Subgroup.isOpen_mono (H₁ := χ.ker.comap (Ine (F := L) (R.s.A v)).subtype)
        (fun x hx => inv_eq_one.2 hx) (hχ.preimage continuous_subtype_val)) fun s => mul_inv_cancel _
    have h4 := ((Loc.laMul h).1 _ _ _ _ _ _ ((Loc.laMul h).1 _ _ _ _ _ _ h2 h3).1 h1).1
    refine ⟨_, h4.1, fun b hb s => ?_⟩
    have h5 := h4.2 b hb s
    rw [hκ _ s.2]
    refine h5.trans ?_
    refine finprod_congr fun τ => ?_
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  choose wt hwt using exists_weights
  refine _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE (j.comp F) (fun v i τ => wt v τ - (e : ℤ) * Fr.w n i) _ (fun x hx => ?_) ⟨fun v τ a b hab => ?_, fun v i => ?_⟩ ?_
    ((UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ n ka).1 r hirr)
  · have h1 : F x = 0 := hF hx
    change j (F x) = 0
    rw [h1, map_zero]
  · have h1 : Fr.w n b < Fr.w n a := by
      have h2 : (a : ℕ) < b := hab
      unfold Fr.w
      split_ifs <;> omega
    have h3 : (0 : ℤ) < e := by exact_mod_cast H.e_pos
    exact sub_lt_sub_left (mul_lt_mul_of_pos_left h1 h3) _
  · let u : c.Oˣ →* (Qbar l)ˣ := Units.map c.O.val.toRingHom.toMonoidHom
    let χ : G L Ω →* (Qbar l)ˣ := ((u.comp (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ L Ω)) ^ Fr.w n i
    have hχ : IsOpen (χ.ker : Set (G L Ω)) := by
      refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker.comap (galEmb ℚ L Ω)) (fun g hg => ?_)
        ((Chr.clsFacts ℚ Ω N).1.preimage (galEmbTop ℚ L Ω).1.continuous)
      have hg' : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 := hg
      dsimp only [χ]
      rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        Chr.dirG, MonoidHom.comp_apply, hg', map_one, map_one, one_zpow]
    have h1 (g : G L Ω) :
        (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) ^ Fr.w n i).val.1 =
          (cycBar L Ω l g ^ ((e : ℤ) * Fr.w n i) * χ g).val := by
      have h : u (chiO ℚ Ω l c.O (galEmb ℚ L Ω g)) = cycBar L Ω l g := Units.ext rfl
      change (u _).val = _
      rw [map_zpow, Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow,
        h, mul_zpow, ← zpow_mul]
      rfl
    refine hwt v _ χ hχ _ fun g hg => Units.ext ?_
    have h2 : F (R.B₀.u.ψ v i g).val = (R.K.twψ ρ₂ v i g).val := congrArg (fun t => (t g).val) (hP v i)
    have h3 := hψ (R.K.e v) i (R.K.lam v g) ((R.K.lam_I v g).2 hg)
    rw [R.lam_j] at h3
    rw [Units.val_mul, ← h1, ← R.κ_pr]
    change j (F (R.B₀.u.ψ v i g).val) = _
    rw [h2]
    exact congrArg (fun t : A => t.1 * (R.K.κ (R.V.pr g)).val.1) h3
  · have h1 : W.UniversalOrdinaryDeterminantRing.Pt.D (j.comp F) = (W.GDet.ofRep (R.K.tw ρ₂)).map (j : c₂.O →+* Qbar l) :=
      congrArg (fun D => D.map (j : c₂.O →+* Qbar l)) hD
    refine (congrArg (fun D => D.comap R.V.pr) h1).trans ?_
    have htw (g : G L Ω) : (tw r ka g).val = ((R.K.tw ρ₂) (R.V.pr g)).map j := by
      rw [tw_val, hr, ← R.κ_pr, ← R.π_pr]
      rfl
    refine W.GDet.ext fun C _ _ x => ?_
    let : Algebra c₂.O C := ((algebraMap (Qbar l) C).comp (j : c₂.O →+* Qbar l)).toAlgebra
    let π : G L Ω →* R.V.frame.G₀ := R.V.pr
    let left := (W.GDet.repAlg (R.K.tw ρ₂) C).toRingHom.comp (MonoidAlgebra.mapDomainRingHom C π)
    let right := (W.GDet.repAlg (W.mat (tw r ka)) C).toRingHom
    change (left x).det = (right x).det
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero left, map_zero right]
    | add a b ha hb => rw [map_add left, map_add right, ha, hb]
    | single g a =>
      change W.GDet.repAlg (R.K.tw ρ₂) C (MonoidAlgebra.mapDomainRingHom C π (MonoidAlgebra.single g a)) =
        W.GDet.repAlg (W.mat (tw r ka)) C (MonoidAlgebra.single g a)
      rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single]
      change a • ((R.K.tw ρ₂) (R.V.pr g)).map (algebraMap c₂.O C) =
        a • ((tw r ka g).val.map (algebraMap (Qbar l) C))
      rw [htw g]
      rfl
theorem UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hMod : _root_.UpperTheory.V.W.ModUAlt) (hLam : W.LamEx)
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
    {ka kb : G L Ω →* (Qbar l)ˣ} (hL : W.Large L c₁) (ha : IsKa σ M ι 2 ka) (hb : IsKa σ M ι 3 kb)
    (e₂ : ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ R : CReal k c₁ f 2 ka, ¬ R.s.p ∣ p₀)
    (e₃ : ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ R : CReal k c₁ f 3 kb, ¬ R.s.p ∣ p₀)
    (s₂ : ∀ (R : CReal k c₁ f 2 ka) J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J)
    (s₃ : ∀ (R : CReal k c₁ f 3 kb) J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J) :
    FinPt c₁.O (Φ.ext f) 3 ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι kb ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka := by
  have one : ∀ (R₂ : CReal k c₁ f 2 ka) (R₃ : CReal k c₁ f 3 kb), FinPt c₁.O (Φ.ext f) 3 ∧
      _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R₃.s.v0 k 3 ι kb ∧ _root_.UpperTheory.Gal.projectedFormsSystemPart.AutPtOAlt R₂.s.v0 k 2 ι ka := fun R₂ R₃ => by
    obtain ⟨J₂, h₂, d₂⟩ := _root_.UpperTheory.V.Pr.modularity_linked_ends hMod hLam ι H v R₂ hL (s₂ R₂)
    obtain ⟨J₃, h₃, d₃⟩ := _root_.UpperTheory.V.Pr.modularity_linked_ends hMod hLam ι H v R₃ hL (s₃ R₃)
    obtain ⟨g₂, g₃, hfin⟩ := UpperTheory.V.Pr.absMain l c₁.O _ R₂.T R₃.T J₂ J₃ h₂ h₃
    exact ⟨hfin, _root_.UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hb J₃ g₃ d₃,
      _root_.UpperTheory.Gal.projectedFormsSystemPart.autPtO_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ ha J₂ g₂ d₂⟩
  obtain ⟨R₂, -⟩ := e₂ 1 one_ne_zero
  obtain ⟨R₃, -⟩ := e₃ 1 one_ne_zero
  obtain ⟨R₂', n₂⟩ := e₂ R₂.s.p R₂.s.p_prime.ne_zero
  obtain ⟨R₃', n₃⟩ := e₃ R₃.s.p R₃.s.p_prime.ne_zero
  obtain ⟨hfin, a₃, a₂⟩ := one R₂ R₃
  obtain ⟨-, b₃, b₂⟩ := one R₂' R₃'
  exact ⟨hfin, fun A _ _ _ ρ h1 h2 r h3 h4 => _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne n₃)
      (a₃ A ρ h1 h2 r h3 h4) (b₃ A ρ h1 h2 r h3 h4),
    fun A _ _ _ ρ h1 h2 r h3 h4 => _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne n₂)
      (a₂ A ρ h1 h2 r h3 h4) (b₂ A ρ h1 h2 r h3 h4)⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
theorem UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → _root_.UpperTheory.V.W.ModUAlt → UpperTheory.V.W.LevEx → UpperTheory.V.W.LamEx → UpperTheory.V.W.ProModularRingExists → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense → _root_.UpperTheory.V.Sd.Seed2Alt → UpperTheory.V.Sd.Twist → UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt := by
  intro hA _ hMod hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ he hev η σ g₁ B M hM hram L _ _ _ _ Φ C₀ k hB hok hbig hseed
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  haveI : IsAlgClosure L Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) L }
  have hM0 : M ≠ 0 := by
    rintro rfl
    obtain ⟨hσ, hc⟩ := k.c
    have h1 : σ ∈ η.ker := k.split ⊤ (by rw [← ValuationSubring.mem_nonunits_iff, Nat.cast_zero]; exact zero_mem _) ⟨by
      refine mem_Dec.2 (eq_top_iff.2 fun x _ => ?_)
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact ValuationSubring.mem_top _, hσ⟩
    have h2 := k.del ⟨σ, hσ⟩
    rw [hc, hok.del_c] at h2
    have h3 : η σ = 1 := h1
    rw [h3] at h2
    exact absurd h2 (by decide)
  have H : UpperTheory.V.Pr.LinkHyp c N e η σ B M := ⟨he, hM, hM0, hram, hB, hD.cc⟩
  have hv : Nonempty Φ.V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hbig.1
    simp [UpperTheory.V.Fr.Frame.d] at this
  obtain ⟨v⟩ := hv
  have hker : η.ker = galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, hka⟩ := hk2 K hker κ hκ
  obtain ⟨c₁, hle, hL, hv3, hv2, f, hf⟩ := UpperTheory.V.Pr.coefEx l c L Ω _ _ hk3.alg.1 hk2.alg.1
  haveI := UpperTheory.V.Pr.coefIs l c₁
  obtain ⟨m₃, hm₃, -, r₃, -, s₃⟩ := hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M hM0
    (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans hM)
    (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M hM L) 2
  obtain ⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩ := hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2
  obtain ⟨hfin, a₃, a₂⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.twoRuns_alt hA hMod hLam ι H v hL hk2 hk3
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl) hok hbig hle hf hk2 hv2)
    (UpperTheory.Gal.projectedFormsSystemPart.cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl) hok hbig hle hf hk3 hv3)
    (fun R₂ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hk2 χ' j hord hcong m₂ hm₂ _ (by
      convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
    (fun R₃ => _root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]))
  exact ⟨UpperTheory.V.Pr.finPtDown l c c₁ f hle hf Φ 3 hfin, a₃, ka, hk2.alg, a₂⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.Sym.Top
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem linkedEnd_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt :=
  have hA := hH.toClassicalTheorems
  have hN := hA.litN
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) levEx (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2
    (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
end UpperTheory.V.Z.Sym.Top
end

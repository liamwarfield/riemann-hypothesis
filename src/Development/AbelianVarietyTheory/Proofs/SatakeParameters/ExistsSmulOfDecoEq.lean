module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
public import Formalism.SharpRestriction.LevelLetterCocycles.CohomologyScalarsVanish.PfCohScalarsVanish
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FramedForms

section Torsor

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem deco_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (a • p).deco = (a.1, a.2.1) • p.deco := rfl

theorem fr_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) (P : Q) :
    (a • p).fr P = a.1.1 * p.fr P * ((a.2.2 P)⁻¹).1 := rfl

theorem exists_smul_of_deco_eq {p q : DecoF E n ST SG Q} (h : p.deco = q.deco) :
    ∃ c : GLQ E n Q, q = ((1, 1, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p := by
  have h' : p.1.1 = q.1.1 := h
  refine ⟨fun P => ⟨(q.fr P)⁻¹ * p.fr P, fun x => ?_⟩, ?_⟩
  · have h1 := q.2 P (((q.fr P)⁻¹ * p.fr P) x)
    have h2 : q.1.2 P (((q.fr P)⁻¹ * p.fr P) x) = p.1.2 P x :=
      LinearEquiv.apply_symm_apply (q.1.2 P) (p.1.2 P x)
    rw [h2, ← h'] at h1
    exact h1.symm.trans (p.2 P x)
  · apply Subtype.ext
    apply Prod.ext
    · exact h'.symm.trans (one_smul (UF E n × GLG (E := E) (n := n) (SG := SG)) p.1.1).symm
    · funext P
      show q.fr P = (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((q.fr P)⁻¹ * p.fr P)⁻¹
      group

theorem stab_inj (p : DecoF E n ST SG Q) {a b : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q}
    (ha : a • p = p) (hb : b • p = p) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  refine Prod.ext h1 (Prod.ext h2 ?_)
  funext P
  have e1 : (a • p).fr P = (b • p).fr P := by rw [ha, hb]
  rw [fr_smul, fr_smul, h1] at e1
  exact inv_injective (Subtype.ext (mul_left_cancel e1))

end Torsor

section Form

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem incl_injective (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    Function.Injective (FrmG.incl Λ Θ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem grp_finiteIndex (Θ : LevQFam X.E X.K n Q) (h : ∀ R : Q, (Θ R).H.FiniteIndex) :
    Θ.grp.FiniteIndex := by
  have h1 : ∀ R : Q, ((Θ R).H.comap (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)).FiniteIndex := by
    intro R
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval R)]
    exact (h R).index_ne_zero
  have h2 := Subgroup.finiteIndex_iInf h1
  refine Subgroup.finiteIndex_of_le (H := ⨅ R : Q, (Θ R).H.comap
    (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)) ?_
  intro c hc
  exact (Subgroup.mem_pi _).mpr fun R _ => Subgroup.mem_iInf.mp hc R

theorem chr_root (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2.1
  obtain ⟨k, hk, hk'⟩ := hΘ g.2.2
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hk2 : ((Θ.chr g.2.2 : X.Kˣ) : X.K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]
  rw [Units.val_mul, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm m k, pow_mul, hk2, one_pow]

theorem frmGSD_ok (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (hfi : ∀ R : Q, (Θ R).H.FiniteIndex)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have := grp_finiteIndex Θ hfi
    let T : Set (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := {d | d ∈ s ∧ ∃ p : DecoF X.E n ST SG Q, p.deco = d}
    have hT : Finite T := hs.subset fun d hd => hd.1
    let S := frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ
    refine Finite.of_surjective (fun x : T × (GLQ X.E n Q ⧸ Θ.grp) =>
      S.cls (((1, 1, (x.2.out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • x.1.2.2.choose)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      have hq : (((g⁻¹, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q)).deco = d0 := by
        rw [deco_smul, hg, smul_smul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        exact one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) d0
      have hd : d0 ∈ T := ⟨hd0, _, hq⟩
      obtain ⟨c, hc⟩ := exists_smul_of_deco_eq (hd.2.choose_spec.trans hq.symm)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Θ.grp c⁻¹
      refine ⟨(⟨d0, hd⟩, (c⁻¹ : GLQ X.E n Q)), ?_⟩
      refine (S.cls_eq_iff _ p).mpr ⟨((g⁻¹, 1, h⁻¹) : FrmG Λ Θ), ?_⟩
      show ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q) =
        ((1, 1, ((c⁻¹ : GLQ X.E n Q) : GLQ X.E n Q ⧸ Θ.grp).out⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
          hd.2.choose
      have e1 : ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) =
          (1, 1, (h : GLQ X.E n Q)⁻¹) * (g⁻¹, 1, 1) := by simp
      rw [e1, mul_smul, hc, smul_smul, hh]
      simp
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).G p =>
        (⟨((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p))) ?_
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (incl_injective Λ Θ
      (stab_inj p a.2 b.2 (Prod.mk.inj h0).1 (Prod.mk.inj h0).2))
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.nab_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.del_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g x y
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    show C.pair (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 x)
      (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv g.1 x y, smul_smul]
    show (star ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem main : ∀ {X : Fields} (_ : X.Ok) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q),
    (∀ R : Q, (Θ R).H.FiniteIndex) → (∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) →
    (frmGSD ((roundPk X lam fun d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => d.1.Lsh).pull DecoF.deco) Λ Θ).Ok := by
  intro X hX n ST SG Q lam Λ Θ h1 h2
  exact frmGSD_ok hX _
    ⟨fun a d => roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2), fun a d => roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2),
      roundPk_inv X _ _ hX.emb_star⟩ Λ Θ h1 h2

end Form

end GlobalTheory.FramedForms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
noncomputable section

namespace GlobalTheory.HOneTwoLevel

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem l_mem_max (N : NData R H what₂) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have hle : (⊤ : Submodule ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i] • ⊤ := by
    intro x _
    have hx : x = ((N.l i : ℕ) : ℤ_[N.l i]) • (((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) * x) := by
      rw [Algebra.smul_def, map_natCast, ← mul_assoc]
      have : ((N.l i : ℕ) : N.O i) * ((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
        exact hu.mul_val_inv
      rw [this, one_mul]
    rw [hx]; exact Submodule.smul_mem_smul hl trivial
  have hjac : IsLocalRing.maximalIdeal ℤ_[N.l i] ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (Module.finite_def.1 inferInstance) hle hjac
  have h1 : (1 : N.O i) ∈ (⊤ : Submodule ℤ_[N.l i] (N.O i)) := trivial
  rw [hbot, Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem isLocalHom (N : NData R H what₂) (i : N.Loc) : IsLocalHom (algebraMap ℤ_[N.l i] (N.O i)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have ha' : a ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := (IsLocalRing.mem_maximalIdeal a).2 h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at ha'
  obtain ⟨c, rfl⟩ := ha'
  have : algebraMap ℤ_[N.l i] (N.O i) (c * (N.l i : ℤ_[N.l i])) ∈ IsLocalRing.maximalIdeal (N.O i) := by
    rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (l_mem_max N i)
  exact (IsLocalRing.mem_maximalIdeal _).1 this ha

theorem resFin (N : NData R H what₂) (i : N.Loc) : Finite (IsLocalRing.ResidueField (N.O i)) :=
  haveI := isLocalHom N i
  IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[N.l i]) inferInstance

theorem resChar (N : NData R H what₂) (i : N.Loc) : CharP (IsLocalRing.ResidueField (N.O i)) (N.l i) := by
  rw [CharP.charP_iff_prime_eq_zero (N.lPrime i).out, ← map_natCast (IsLocalRing.residue (N.O i)),
    IsLocalRing.residue_eq_zero_iff]
  exact l_mem_max N i

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

theorem chiEpsBar_open (N : NData R H what₂) (i : N.Loc) (e : ℤ) :
    IsOpen ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  have hmZ : IsOpen (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) := by
    have : (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) = {x | ‖x‖ < 1} := by
      ext x
      simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, Set.mem_setOf_eq]
      exact PadicInt.mem_nonunits
    rw [this]; exact isOpen_lt continuous_norm continuous_const
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  let U2 : Set (G H.E N.Om) :=
    (fun g => ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ⁻¹'
      (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i])
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have hU2 : IsOpen U2 :=
    hmZ.preimage ((Units.continuous_val.comp (continuous_cycZ H.E N.Om (N.l i))).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 ∩ U2 := by
    refine ⟨?_, ?_⟩
    · show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
    · show ((cycZ H.E N.Om (N.l i) 1 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[N.l i]
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ∩ U2 ⊆ ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
    intro g hg
    have ha : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1 := by
      ext
      exact residue_eq_one N i hg.1
    have hb : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (Formalism.MainNotions.N.Glob.epsO N i g) = 1 := by
      ext
      apply residue_eq_one N i
      have := isLocalHom N i
      have h2 : ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈
          IsLocalRing.maximalIdeal ℤ_[N.l i] := hg.2
      have h3 : algebraMap ℤ_[N.l i] (N.O i)
          (((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ∈ IsLocalRing.maximalIdeal (N.O i) :=
        (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          (IsLocalRing.mem_maximalIdeal _).1 h2 (isUnit_of_map_unit _ _ hu)
      rw [map_sub, map_one] at h3
      exact h3
    show Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e g = 1
    delta Formalism.MainNotions.SumRepresentations.At.chiEpsBar
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ha, hb, inv_one, one_zpow, one_mul]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset ((hU1.inter hU2).mem_nhds h1) hsub)

theorem contAction_of_open {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation k Γ M) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (h1 : ∀ u ∈ U, rho u = 1) : ReciprocityTheory.Gal.ContAction rho := by
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, m⟩
  have hU' : (fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ) ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using U.one_mem)
  have hm : ({m} : Set M) ∈ 𝓝 m := (isOpen_discrete _).mem_nhds rfl
  filter_upwards [prod_mem_nhds hU' hm] with x hx
  have hx2' : x.2 = m := hx.2
  have hx1' : g⁻¹ * x.1 ∈ U := hx.1
  show rho x.1 x.2 = rho g m
  calc rho x.1 x.2 = rho (g * (g⁻¹ * x.1)) m := by rw [mul_inv_cancel_left, hx2']
    _ = rho g (rho (g⁻¹ * x.1) m) := by rw [map_mul]; rfl
    _ = rho g m := by rw [h1 _ hx1']; rfl

theorem twist_sub_bijective {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (c : k) (hc : c ≠ 0)
    (hne : ¬ A.charpoly.IsRoot c) :
    Function.Bijective (fun v : Fin n → k => c⁻¹ • Matrix.toLin' A v - v) := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • Matrix.toLin' A - LinearMap.id
  have hf : ∀ v, f v = c⁻¹ • Matrix.toLin' A v - v := fun v => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, hf, sub_eq_zero] at hv
    rw [Submodule.mem_bot]
    by_contra h0
    apply hne
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    have hAv : Matrix.toLin' A v = c • v := by
      calc Matrix.toLin' A v = c • (c⁻¹ • Matrix.toLin' A v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hAv, h0⟩
  have hbij : Function.Bijective f := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  exact hbij

theorem hOneTwo_holds : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  intro hF hT hE D i rb w hwS hrb hnr e
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w (Or.inl hwS)
  haveI := resFin D.nd i
  haveI := resChar D.nd i
  letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
  haveI : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    Module.compHom _ (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)))
  haveI : ContinuousConstSMul (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  let rho := (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e)).comp
    (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype
  let rhoZ : Representation (ZMod (D.nd.l i ^ 1)) ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))
      (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add (rho g)
          map_smul' := fun c m => map_smul (rho g)
            (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) c) m }
      map_one' := LinearMap.ext fun m => show rho 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show rho (g * h) m = rho g (rho h m) by
        rw [map_mul]; rfl }
  have hrZ : ∀ g m, rhoZ g m = rho g m := fun _ _ => rfl

  have hU : IsOpen (((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype : Subgroup _) :
        Set ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) :=
    (hrb.1.inter (chiEpsBar_open D.nd i e)).preimage continuous_subtype_val
  have h1U : ∀ u ∈ ((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype), rhoZ u = 1 := by
    intro u hu
    have hu' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hu)
    have ha : rb (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.1
    have hc : Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.2
    apply LinearMap.ext
    intro v
    show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) :
        (IsLocalRing.ResidueField (D.nd.O i))ˣ) : IsLocalRing.ResidueField (D.nd.O i)) •
        Matrix.toLin' ((rb (u : G D.host.E D.nd.Om) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v = v
    rw [ha, hc]
    simp
  have hcZ : ContAction rhoZ := contAction_of_open _ _ hU h1U

  have hγD : D.nd.gam0 i w ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i w)
  have hc0 : IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)) ≠ 0 :=
    ((Units.isUnit (D.nd.chi i 1 (D.nd.gam0 i w))).map (IsLocalRing.residue (D.nd.O i))).ne_zero
  have hbij : Function.Bijective (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
      rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) := by
    have h2 : (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
        rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) = fun v =>
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))⁻¹ •
          Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v := by
      funext v
      show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (D.nd.gam0 i w) : (IsLocalRing.ResidueField (D.nd.O i))ˣ) :
        IsLocalRing.ResidueField (D.nd.O i)) • Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v = _
      rw [Formalism.MainNotions.SumRepresentations.twisted_character_at_frobenius D.nd w hw e]
    rw [h2]
    exact twist_sub_bijective _ _ hc0 hnr
  have key := GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed hF hT hE D.host.E D.nd.Om (D.nd.l i)
    (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) (D.nd.plOm.1 w) w rhoZ (D.nd.plOm.2 w) hw hcZ
    ⟨⟨D.nd.gam0 i w, hγD⟩, D.nd.locNd_chebotarevPlace_mem i w, hbij⟩
  have hk := Formalism.MainNotions.N.CohomologyScalarsVanish.cohScalarsVanish (D.nd.l i ^ 1) (IsLocalRing.ResidueField (D.nd.O i))
    ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) rho rhoZ hrZ key
  exact ⟨hk.2.1, hk.2.2⟩

end GlobalTheory.HOneTwoLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDualityStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  first | exact @GlobalTheory.HOneTwoLevel.hOneTwo_holds | exact GlobalTheory.HOneTwoLevel.hOneTwo_holds | (intros; apply GlobalTheory.HOneTwoLevel.hOneTwo_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open TensorProduct Formalism.UG Formalism.UG.P

namespace GlobalTheory.OpenChrRam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    (N : v.adicCompletion F) ≠ 0 ∧ (N : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (N : v.adicCompletion F) = 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) := by simp
    have e2 : v.valuation F (algebraMap (𝓞 F) F (N : 𝓞 F)) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hN
    rw [← e2, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact congrArg _ e
  refine ⟨fun h => by rw [h] at h1; simp at h1, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem inertAt_le_congN (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  rintro x ⟨⟨hx, hx'⟩, hs⟩
  obtain ⟨hN0, hNi⟩ := inv_natCast_mem v N hN
  let u : (RInt F E)ˣ := ⟨⟨x, hx⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx'⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  have hn : (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, afsplitI_mem_intAd v _ hNi⟩, rfl⟩)
  refine (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2 ⟨⟨_, hn⟩ * ((u : RInt F E) - 1), ?_⟩)
  apply Subtype.ext
  show (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ * ((x : AfE F E) - 1) * ((N : RInt F E) : AfE F E)
    = (x : AfE F E) - 1
  rw [SubringClass.coe_natCast, ← sub_eq_zero]
  refine afsplit_inj _ fun w => ?_
  rw [map_sub, map_mul, map_mul, afsplit_prV_tmul, map_natCast]
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, mul_right_comm]
    have : (1 : E) ⊗ₜ[F] (N : w.adicCompletion F)⁻¹ * (N : E ⊗[F] w.adicCompletion F) = 1 := by
      have e : (N : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ[F] (N : w.adicCompletion F) :=
        (map_natCast (Algebra.TensorProduct.includeRight :
          w.adicCompletion F →ₐ[F] E ⊗[F] w.adicCompletion F) N).symm
      rw [e, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hN0, one_mul]
      rfl
    rw [this, one_mul, sub_self]
  · have hw : prV (E := E) w (x : AfE F E) = 1 := by
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hs w) h
      exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
    rw [map_sub, hw, map_one, sub_self, mul_zero, zero_mul, sub_self]

theorem qprime_finite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (L : Type) [Field L] (ξ : Chr F E L) (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  by_contra hc
  refine hv ((inertAt_le_congN v N fun hm => hc ?_).trans hk)
  exact Ideal.dvd_span_singleton.2 hm

end GlobalTheory.OpenChrRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).Box := by
  intro D L C j ε τ φ hR
  have hb := (GlobalTheory.T.roundedSizeBound_window L C hR).1
  have hw := (GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C hR).2.2
  have hnt := fun g => GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR
  have hth := fun g => GlobalTheory.T.floor_size_bounds_at_thick_embedding L g j
  obtain ⟨hC, h100, hroom, hwb, -, hCb⟩ := hR
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := L.t_win.1
  have ht' : 1 ≤ D.R.t := by exact_mod_cast ht
  have hLw : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : 0 ≤ L.sc.b' := by linarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by
    have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hb'
    linarith
  have hw0 : (0 : ℝ) ≤ wHat D := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
  have hE : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold etaHat
    push_cast
    have := Nat.floor_le hη.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ bHat L
    have : (1 : ℝ) ≤ bHat L := by linarith
    exact_mod_cast this
  · show 1 ≤ wHat D
    unfold wHat
    omega
  · show 20 * wHat D ≤ bHat L
    have : (20 : ℝ) * wHat D ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * etaHat L ≤ bHat L
    have : (20 : ℝ) * etaHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * sHat L ≤ bHat L
    have : (20 : ℝ) * sHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · intro i
    show ((etaHat L : ℕ) : ℤ) < szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
    generalize letter τ φ i = g
    have hsz : L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by
      by_cases hT : Thick D.host g
      · have := (hth g hT).1
        linarith
      · exact (hnt g hT).1
    have key : ((etaHat L : ℕ) : ℤ) + D.R.t + 1 < ⌊(hcAt D g).e j⌋ := by
      have : ((etaHat L : ℕ) : ℝ) + D.R.t + 1 < (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    unfold szT
    split_ifs <;> omega

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).Box := by
  first | exact @GlobalTheory.HTW.pageWord_box | exact GlobalTheory.HTW.pageWord_box | (intros; apply GlobalTheory.HTW.pageWord_box <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom (P : HeightOneSpectrum (𝓞 E)) : intSub P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

theorem redHom_apply (P : HeightOneSpectrum (𝓞 E)) (a : intSub P) : redHom P a = redP P a.1 := rfl

variable [StarRing E]

theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem eN_mem (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt]
  intro j
  unfold Loc.eN
  split_ifs
  · simpa using IntAt.coe P 1
  · simpa using IntAt.coe P 0

theorem intAt_entry (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) (i j : ℕ) : IntAt P (Loc.atN (g (Loc.eN E N j)) i) := by
  have hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P := hg
  have hm : g (Loc.eN E N j) ∈ stdAt E N P := (hg' _).2 (eN_mem P N j)
  rw [mem_stdAt] at hm
  unfold Loc.atN
  split_ifs with h
  · exact hm _
  · simpa using IntAt.coe P 0

def blockD (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P) :=
  Matrix.of fun s t => ⟨Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1), intAt_entry P hg _ _⟩

theorem redP_det_block (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) :
    redP P (Matrix.det (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1))) =
      ((redHom P).mapMatrix (blockD P kj n hg)).det := by
  have h1 : (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) =
      (intSub P).subtype.mapMatrix (blockD P kj n hg) := by
    ext s t
    rfl
  rw [h1, ← RingHom.map_det, ← RingHom.map_det]
  rfl

end GlobalTheory.TwistRowType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  intro D L C j ε τ φ hR i
  by_cases h : Thick D.host (letter τ φ i)
  · exact Or.inl ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  · right
    have h1 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 _ j h
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) ≤ ((wHat D : ℕ) : ℤ)
    unfold szT wHat
    push_cast
    split_ifs <;> omega

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOrStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  first | exact @GlobalTheory.HTW.pageWord_thickOr | exact GlobalTheory.HTW.pageWord_thickOr | (intros; apply GlobalTheory.HTW.pageWord_thickOr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSets
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSets
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow


open Formalism.MainNotions.AdmissibleParameterJ in
theorem JJ_finite_ncard {D : D7} (L : SizeData₂ D) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hn : 0 < D.R.nV) (up : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite ∧ (JJ D up j ρ).ncard = D.R.nV := by
  have hc : (Jp D j ρ).ncard = D.R.nV := (hb j h1 h2 ρ).2.2.2.2.2
  have hf : (Jp D j ρ).Finite := Set.finite_of_ncard_pos (by omega)
  cases up with
  | true => simpa [JJ] using And.intro hf hc
  | false =>
    have hinj : Function.Injective (AdmissibleParameterJ.refl D) := by
      intro a b hab
      simp only [AdmissibleParameterJ.refl] at hab
      linarith
    have hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ := by
      ext q
      simp only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨_, h, by simp [AdmissibleParameterJ.refl]⟩
      · rintro ⟨u, hu, rfl⟩
        have : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u := by simp [AdmissibleParameterJ.refl]
        rwa [this]
    simp only [JJ, Bool.false_eq_true, if_false]
    rw [hEq]
    exact ⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩

theorem jumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  classical
  intro D large₂ hJ hP
  obtain ⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩ := hJ
  have hn : 0 < D.R.nV := by
    have := D.R.rank_add_five_le
    unfold Ranks.nV; omega
  have hS := large₂.Sc_pos
  have hη := large₂.etaSz_pos
  have hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b := hP
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Nat.le_floor (by linarith), ?_⟩
  intro i r hr π w hw CL h τ
  obtain ⟨g, ρ, -, hx, -⟩ := hA i r hr w hw ⟨CL, h⟩ τ
  have hj := D.nd.j_range i
  obtain ⟨hfin, hcard⟩ := JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ
  have hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite :=
    hfin.preimage (Int.cast_injective.injOn)
  refine ⟨hpre.toFinset, ?_, ?_, ?_⟩
  · rw [← hcard, ← Set.ncard_eq_toFinset_card _ hpre,
      ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]
    exact Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin
  · intro u hu
    have hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := by
      simpa using hu
    have hbd := he.1 _ hj.1 hj.2 ρ _ _ hu'
    have hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
      simp [AdmissibleParameterJ.c0]
    rw [hc0] at hbd
    have habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)| := by
      simp [Nat.cast_natAbs]
    have hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [habs]
      linarith
    omega
  · intro a ha
    have : (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := (hx π a).1.1 ha
    simpa using this

end GlobalTheory.BlockWindow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSetsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  first | exact @GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | exact GlobalTheory.BlockWindow.jumpWindow_of_jumpSets | (intros; apply GlobalTheory.BlockWindow.jumpWindow_of_jumpSets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

namespace RowTypeInv

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE

section Alg

variable {R : Type*} [CommRing R]

end Alg

section Red

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_one : IntAt P (1 : E) := by simpa using IntAt.coe P 1

theorem intAt_zero : IntAt P (0 : E) := by simpa using IntAt.coe P 0

theorem reduction_one₂ : redP P (1 : E) = 1 := by simpa using reduction_coe P 1

theorem reduction_zero : redP P (0 : E) = 0 := by simpa using reduction_coe P 0

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := intAt_one P
  add_mem' := IntAt.add
  zero_mem' := intAt_zero P
  neg_mem' := fun {a} ha => by
    have := (IntAt.coe P (-1)).mul ha
    simpa using this

noncomputable def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := reduction_one₂ P
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := reduction_zero P
  map_add' a b := reduction_add a.2 b.2

theorem reduction_sum₂ {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h := map_sum (redHom P) (fun i => (⟨f i, hf i⟩ : intRing P)) s
  have h2 : ((∑ i ∈ s, (⟨f i, hf i⟩ : intRing P) : intRing P) : E) = ∑ i ∈ s, f i := by
    simp
  rw [← h2]
  exact h

theorem reduction_det {t : ℕ} (A : Matrix (Fin t) (Fin t) E) (hA : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let B : Matrix (Fin t) (Fin t) (intRing P) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have h1 : (B.det : E) = A.det := by
    have := (intRing P).subtype.map_det B
    exact this
  have h2 := (redHom P).map_det B
  rw [← h1]
  exact h2


end Red

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem mem_sclLat (N : ℕ) (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  simp



variable {P q} {k₀ r t n : ℕ} {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)}

end Ent

end RowTypeInv


end GlobalTheory
end

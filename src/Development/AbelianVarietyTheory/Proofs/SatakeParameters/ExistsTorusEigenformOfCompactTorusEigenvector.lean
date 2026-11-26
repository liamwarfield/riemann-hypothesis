module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TorusEigenform

section General

variable {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]

theorem exists_char_of_isIrreducible {σ : Representation ℂ G V} (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ μ : G →* ℂˣ, ∀ g w, σ g w = (μ g : ℂ) • w := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : ∀ g, ∃ c : ℂ, ∀ w, σ g w = c • w := fun g =>
    LocGL.exists_eq_smul_of_isSmooth hs hi
      ⟨σ g, fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]⟩
  choose c hc using h
  let m : G →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by simp [← hc])
      map_mul' := fun a b => smul_left_injective ℂ hv (by
        show c (a * b) • v = (c a * c b) • v
        rw [← hc, map_mul, Module.End.mul_apply, hc b, hc a, smul_smul]) }
  exact ⟨m.toHomUnits, fun g w => hc g w⟩

theorem exists_eigenform {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) {x : V} (hx : x ≠ 0)
    (hxH : ∀ t ∈ H, ρ t x = (χ t : ℂ) • x) :
    ∃ (μ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (μ g : ℂ) * l v) ∧ ∀ h ∈ H, μ h = χ h := by
  let ρ' := SmGL.twist ρ χ⁻¹
  have hρ' : ∀ g v, ρ' g v = ((χ g)⁻¹ : ℂˣ) • ρ g v := fun _ _ => rfl
  have hc := LocGL.isCompl_fixed_twKer (isSmooth_twist hρ hχ.inv) hH
  let T : Subrepresentation ρ := ⟨twKer ρ' H 1, fun g v hv => by
    have h1 : ρ' g v ∈ twKer ρ' H 1 :=
      twKer_le_comap ρ' H g (by rw [Subgroup.normalizer_eq_top]; trivial) hv
    have h2 := (twKer ρ' H 1).smul_mem (χ g : ℂ) h1
    rwa [hρ', ← Units.smul_def, smul_inv_smul] at h2⟩
  have hT : T ≠ ⊤ := fun h => by
    have h1 : x ∈ T.toSubmodule := by rw [h]; trivial
    have h2 : x ∈ fixed ρ' H := fun t => by
      rw [hρ', hxH t t.2, ← Units.smul_def, inv_smul_smul]; simp
    exact hx ((Submodule.disjoint_def.1 hc.disjoint) x h2 h1)
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  refine ⟨μ, l, hl0, hle, fun h hh => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hl0 (LinearMap.ext hn)
  have h1 : ρ' h v - v ∈ T.toSubmodule := Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
  have h2 := hlM (hTM h1)
  rw [LinearMap.mem_ker, map_sub, hρ', Units.smul_def, map_smul, hle, sub_eq_zero, smul_eq_mul,
    ← mul_assoc] at h2
  have h3 := mul_right_cancel₀ hv (h2.trans (one_mul _).symm)
  rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h3
  exact h3.symm

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountableTopology_units : SecondCountableTopology kˣ := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  exact Units.isEmbedding_val₀.secondCountableTopology

variable {k} in
theorem isSmoothChar_torusChar {n : ℕ} {θ : Fin n → kˣ →* ℂˣ} (hθ : ∀ i, IsSmoothChar (θ i)) :
    IsSmoothChar (SmGL.torusChar θ) :=
  Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) (by
    show IsOpen _
    rw [MonoidHom.ker_one]
    exact isOpen_univ) fun i _ => (hθ i).comp _ (continuous_apply i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (SmGL.torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (SmGL.torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  intro k _ _ _ _ n V _ _ ρ x θ hρ hl hθ hx hxH
  haveI := secondCountableTopology_units k
  obtain ⟨μ, l, hl0, hle, hμ⟩ := exists_eigenform hρ hl (SmGL.UnramFixed.isCompact_torusO k (Fin n))
    (isSmoothChar_torusChar hθ) hx hxH
  refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), l, hl0, fun t y => ?_, fun i u hu => ?_⟩
  · rw [hle, SmGL.torusChar_apply]
    conv_lhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  · have h := hμ (Pi.mulSingle i u) fun j => by
      by_cases h : j = i
      · subst h; simpa using hu
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [SmGL.torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same] at h
    exact h

end GlobalTheory.TorusEigenform
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (GlobalTheory.SmGL.torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  first | exact @GlobalTheory.TorusEigenform.main | exact GlobalTheory.TorusEigenform.main | (intros; apply GlobalTheory.TorusEigenform.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPart
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaUp_injective_on_carried : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hB hP p c hc w hw hw0 hadj
  have hwp : w ∈ R.EEp3 p := by
    unfold RealDat3.EEp3
    exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.EEc c) c hc) hw
  have h := hB A3.A.μ0 p w hwp
  rw [LinearMap.comp_apply, hadj, map_zero] at h
  have hpos : 0 < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    refine mul_pos hP.1 (Finset.prod_pos fun j _ => ?_)
    unfold RealDat3.lamN
    split_ifs
    · exact hP.2 _ _ _
    · exact one_pos
  have hne : (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact hw0 ((smul_eq_zero.1 h.symm).resolve_left hne)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upward_theta_lift_injective_on_carried_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  first | exact @GlobalTheory.thetaUp_injective_on_carried | exact GlobalTheory.thetaUp_injective_on_carried | (intros; apply GlobalTheory.thetaUp_injective_on_carried <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SqrtNegPrimeMemKur
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKsOfKur
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN.SelfGood

variable {l : ℕ} [Fact l.Prime]

theorem sqrt_mem (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) (S : IntermediateField ℚ_[l] (Loc.Om l))
    (hS : ∀ z : Loc.Om l, z ^ p = 1 → z ∈ S) (x : Loc.Om l) (hx : x ^ 2 = -(p : Loc.Om l)) : x ∈ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Loc.Om l) p
  let ψ : AddChar (ZMod p) (Loc.Om l) := AddChar.zmodChar p hw.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hw
  let χ : MulChar (ZMod p) (Loc.Om l) := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom (Loc.Om l))
  have hch : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hneg : χ (-1) = -1 := by
    have : quadraticChar (ZMod p) (-1) = -1 := by
      rw [quadraticChar_neg_one hch, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    simp [χ, MulChar.ringHomComp_apply, this]
  have hmu : ∀ a, ψ a ∈ S := fun a => hS _ (by
    rw [AddChar.zmodChar_apply, ← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow])
  have hg : gaussSum χ ψ ^ 2 = -(p : Loc.Om l) := by
    rw [gaussSum_sq hχ1 hχq hψ, hneg, ZMod.card]; simp
  have hm : gaussSum χ ψ ∈ S := by
    unfold gaussSum
    exact sum_mem fun a _ => mul_mem (intCast_mem _ _) (hmu a)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hg.symm) with h | h
  · rw [h]; exact hm
  · rw [h]; exact neg_mem hm

theorem root_mem_Kur {z : Loc.Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : z ^ m = 1) :
    z ∈ Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

end GlobalTheory.MemN.SelfGood
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.SqrtUnram

theorem sqrt_neg_prime_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), q.Prime → q % 4 = 3 → l ≠ q →
    ∀ x : PadicAlgCl l, x ^ 2 = -(q : PadicAlgCl l) → x ∈ Loc.MaximalUnramifiedExtension l := by
  intro l _ q hq h4 hne x hx
  exact GlobalTheory.MemN.SelfGood.sqrt_mem q hq h4 _
    (fun z hz => GlobalTheory.MemN.SelfGood.root_mem_Kur hq.pos
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).1 hd)) hz) x hx

end GlobalTheory.SqrtUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {H : Subgroup G} (hH : IsCompact (H : Set G))

include hρ hH in
theorem idem_comm (T : Module.End ℂ V) (hT : ∀ g, T * ρ g = ρ g * T) (v : V) :
    T (GlobalTheory.LocGL.idem hρ hH v) = GlobalTheory.LocGL.idem hρ hH (T v) := by
  have h1 : v - GlobalTheory.LocGL.idem hρ hH v ∈ GlobalTheory.PRep.twKer ρ H 1 := (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).1 (by
    rw [map_sub, GlobalTheory.LocGL.idem_of_mem hρ hH (GlobalTheory.LocGL.idem_mem hρ hH v), sub_self])
  have h2 : T (v - GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.twKer ρ H 1 := by
    refine (Submodule.span_le (p := (GlobalTheory.PRep.twKer ρ H 1).comap T)).2 ?_ h1
    rintro _ ⟨n, w, rfl⟩
    refine Submodule.subset_span ⟨n, T w, ?_⟩
    rw [map_sub, map_smul]
    exact congrArg (· - _) (LinearMap.congr_fun (hT n) w)
  have h3 : T (GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.fixed ρ H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← Module.End.mul_apply, ← hT, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 (GlobalTheory.LocGL.idem_mem hρ hH v) k hk]
  rw [show T v = T (GlobalTheory.LocGL.idem hρ hH v) + T (v - GlobalTheory.LocGL.idem hρ hH v) by rw [← map_add (f := _), add_sub_cancel],
    map_add, GlobalTheory.LocGL.idem_of_mem hρ hH h3, (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).2 h2, add_zero]

end Gen

section Cusp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem op_comm_fin (π : CuspSub E a) (o : Op E a) (ho : ∀ k, o ≠ .fin k) (g : GL (Fin a) (Af E)) (y : π.V) :
    π.op o (π.finPart g y) = π.finPart g (π.op o y) := by
  refine Subtype.ext ?_
  cases o with
  | fin k => exact (ho k rfl).elim
  | cpt u =>
    change (rt E a (infGL E a (Unitary.toUnits u)) * rt E a (finGL E a g)) y.1 =
      (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits u))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X => exact LinearMap.congr_fun (lie_rt_fin X g) y.1

theorem bot_or_top (π : CuspSub E a) (W : Submodule ℂ π.V) (h : ∀ o, ∀ x ∈ W, π.op o x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, h o x hx, rfl⟩) with e | e
  · exact Or.inl (hi (e.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (e.trans (Submodule.map_subtype_top _).symm))

end Cusp

end GlobalTheory.TwistRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_conj_mem {a : ℕ} (ha : 1 ≤ a) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (v.adicCompletion E))
    (u : (v.adicCompletion E)ˣ) (hu : IsUnitAt v u) :
    ∃ h ∈ GlobalTheory.LFun.KGL v (n := a), g⁻¹ * h * g ∈ GlobalTheory.LFun.KGL v (n := a) ∧ GeneralLinearGroup.det h = u := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have hK : GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL v (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion v a
  obtain ⟨x, hx, y, hy, t, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT (n := Fin a) g
  rw [hK] at hx hy
  have hu1 : Valued.v (u : v.adicCompletion E) ≤ 1 := le_of_eq hu
  have hu2 : Valued.v ((u⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (u : v.adicCompletion E) = 1 from hu, inv_one]
  let u' : (Formalism.UG.Ov E v)ˣ := ⟨⟨u, hu1⟩, ⟨(u⁻¹ : (v.adicCompletion E)ˣ), hu2⟩,
    Subtype.ext (Units.mul_inv u), Subtype.ext (Units.inv_mul u)⟩
  let i₀ : Fin a := ⟨0, ha⟩
  let d := GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) (Pi.mulSingle i₀ u)
  have hd : d ∈ GlobalTheory.LFun.KGL v (n := a) := by
    refine ⟨GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u'), Units.ext ?_⟩
    change ((Formalism.UG.Ov E v).subtype.mapMatrix (GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u')).val :
      Matrix (Fin a) (Fin a) (v.adicCompletion E)) = (d : Matrix (Fin a) (Fin a) (v.adicCompletion E))
    rw [GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi; simp [u']
      · simp [hi]
    · simp [hij]
  have hdt : (GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t)⁻¹ * d * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t = d := by
    rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  refine ⟨x * d * x⁻¹, mul_mem (mul_mem hx hd) (inv_mem hx), ?_, ?_⟩
  · have e : (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y)⁻¹ * (x * d * x⁻¹) *
        (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y) = y⁻¹ * d * y := by
      conv_rhs => rw [← hdt]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hy) hd) hy
  · have hdet : GeneralLinearGroup.det d = u := by
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal]
      rw [Finset.prod_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp
    rw [map_mul, map_mul, map_inv, hdet, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_locGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (Af E))
    (h : GL (Fin a) (v.adicCompletion E)) :
    g⁻¹ * locGL E a v h * g = locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
      GeneralLinearGroup.map (pLoc E v) g) := by
  have key : ∀ w, GeneralLinearGroup.map (pLoc E w) (g⁻¹ * locGL E a v h * g) =
      GeneralLinearGroup.map (pLoc E w) (locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g)) := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, map_mul, map_mul, map_inv, pLoc_locGL]
    · rw [pLoc_locGL_of_ne hw, map_mul, map_mul, pLoc_locGL_of_ne hw, mul_one, map_inv, inv_mul_cancel]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun w => ?_)
  exact congrArg (fun M : GL (Fin a) (w.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
    (key w)

end Local

end GlobalTheory.TwistRamified

namespace GlobalTheory.TwistRamified

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem no_eigvec (p : CuspSub E a) (ha : 1 ≤ a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (hη : ¬ η.UnrAt v)
    {x : p.V} (hx : x ∈ GlobalTheory.PRep.fixed (p.locRep v) (GlobalTheory.LFun.KGL v (n := a))) (hx0 : x ≠ 0) (y : p.V)
    (hy : ∀ k ∈ GlobalTheory.LFun.KGL v (n := a), p.locRep v k y = ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • y) : y = 0 := by
  set χ := CuspSub.locDet a η v with hχdef
  have hχs : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := GlobalTheory.SmGL.IsSmoothChar.inv (CuspSub.isOpen_ker_locDet (a := a) η v)
  have hρ := p.isSmooth_locRep v
  have hρ' := GlobalTheory.SmGL.isSmooth_twist hρ hχs
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v a).2
  set P := GlobalTheory.LocGL.idem hρ' hK with hPdef
  have hρ'app : ∀ g z, GlobalTheory.SmGL.twist (p.locRep v) χ⁻¹ g z = ((χ g : ℂˣ) : ℂ)⁻¹ • p.locRep v g z := fun g z => by
    simp

  have hPeq : ∀ k ∈ GlobalTheory.LFun.KGL v (n := a), ∀ z, P (p.locRep v k z) = ((χ k : ℂˣ) : ℂ) • P z := fun k hk z => by
    have h1 := GlobalTheory.LocGL.idem_apply_mem hρ' hK hk z
    rw [hρ'app, map_smul] at h1
    rw [← h1, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hPfix : P y = y := by
    refine GlobalTheory.LocGL.idem_of_mem hρ' hK (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_)
    rw [hρ'app, hy k hk, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hPzero : ∀ z, ∀ h ∈ GlobalTheory.LFun.KGL v (n := a), χ h ≠ 1 → p.locRep v h z = z → P z = 0 := fun z h hh hc hz => by
    have h1 := hPeq h hh z
    rw [hz] at h1
    have h2 : (((χ h : ℂˣ) : ℂ) - 1) • P z = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    refine (smul_eq_zero.1 h2).resolve_left fun h0 => hc (Units.ext ?_)
    rw [Units.val_one]; exact sub_eq_zero.1 h0

  have hPcomm : ∀ o : Op E a, (∀ k, o ≠ .fin k) → ∀ z, P (p.op o z) = p.op o (P z) := fun o ho z => by
    have h1 := idem_comm hρ' hK (p.op o) (fun g => by
      refine LinearMap.ext fun w => ?_
      simp only [Module.End.mul_apply, hρ'app, map_smul]
      congr 1
      exact op_comm_fin p o ho (locGL E a v g) w) z
    exact h1.symm

  have hPx : ∀ g : GL (Fin a) (Af E), P (p.finPart g x) = 0 := fun g => by
    obtain ⟨u, hu, hu1⟩ : ∃ u, IsUnitAt v u ∧ η.loc v u ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hη hc
    obtain ⟨h, hh, hgh, hdet⟩ := exists_conj_mem ha v (GeneralLinearGroup.map (pLoc E v) g) u hu
    refine hPzero _ h hh (by rw [hχdef, CuspSub.locDet, MonoidHom.comp_apply, hdet]; exact hu1) ?_
    have e : locGL E a v h * g = g * locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g) := by
      rw [← conj_locGL]; group
    change p.finPart (locGL E a v h) (p.finPart g x) = _
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    congr 1
    exact GlobalTheory.LGrp.mem_fixed.1 hx _ hgh

  let W : Submodule ℂ p.V :=
    { carrier := {φ | ∀ g, P (p.finPart g φ) = 0}
      add_mem' := fun {φ ψ} hφ hψ g => by rw [map_add (f := _), map_add (f := _), hφ g, hψ g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c φ hφ g => by
        change P (p.finPart g (c • φ)) = 0
        rw [map_smul, map_smul, hφ g, smul_zero] }
  have hW : ∀ o, ∀ φ ∈ W, p.op o φ ∈ W := by
    intro o φ hφ g
    by_cases ho : ∀ k, o ≠ .fin k
    · rw [← op_comm_fin p o ho, hPcomm o ho]
      change p.op o (P (p.finPart g φ)) = 0
      rw [hφ g, map_zero]
    · push_neg at ho
      obtain ⟨k, rfl⟩ := ho
      have e : p.finPart g (p.op (.fin k) φ) = p.finPart (g * k) φ := by
        rw [map_mul, Module.End.mul_apply]; rfl
      rw [e]
      exact hφ (g * k)
  rcases bot_or_top p W hW with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (show x ∈ W from hPx))) hx0
  · have h1 : y ∈ W := h ▸ Submodule.mem_top
    have h2 := h1 1
    rwa [map_one, Module.End.one_apply, hPfix] at h2

end GlobalTheory.TwistRamified

theorem GlobalTheory.TwistRamified.twist_ne : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v →
    π.twist η ≠ π := by
  intro E _ _ _ a ha π η v B hB hη
  induction π using Quotient.inductionOn with | _ p => ?_
  intro e
  obtain ⟨T, hT⟩ : CuspSub.Iso (p.twist η) p := Quotient.exact e
  have hB' : GlobalTheory.LFun.HasSatGL v (p.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL v (n := a), p.locRep v k (T (p.toTwist η x)) =
      ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • T (p.toTwist η x) := fun k hk => by
    rw [CuspSub.locRep_eq, ← hT, CuspSub.op_toTwist, ← CuspSub.locRep_eq, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
    simp only [opAdd, zero_smul, add_zero, map_smul]
    congr 2
    exact CuspSub.chiDet_locGL η v k
  have h0 := GlobalTheory.TwistRamified.no_eigvec p ha η v hη hx hx0 _ hy
  have ht : p.toTwist η x = 0 := T.injective (h0.trans T.map_zero.symm)
  exact hx0 ((p.toTwist η).injective (ht.trans (p.toTwist η).map_zero.symm))
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelfStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_ramified_char_ne_self : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v → π.twist η ≠ π := by
  first | exact @GlobalTheory.TwistRamified.twist_ne | exact GlobalTheory.TwistRamified.twist_ne | (intros; apply GlobalTheory.TwistRamified.twist_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

open Formalism.L2.NTheta GlobalTheory.SplitPlace GlobalTheory.DualSplitRel

variable {D : D7}

theorem split_of_primeIdem {P : Pl D.host.E} (hP : conjPl P ≠ P) {e f : AE D} (h : IsPrimeIdem P e f) :
    IsIdemAt e P ∧ f = e + cA D e := by
  rcases h with h | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact h
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem dual_shift (d : List ℤ) : dualLab ((dualLab (d.map fun x => x - 1)).map (· - 1)) = d := by
  simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]

theorem shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ} {R : Finset (GA D V)} [DecidableEq (GA D V)]
    (hR : SphOp V P d R) : ∃ z : GA D V, (∀ γ ∈ R, γ * z = z * γ) ∧
      SphOp V P (splitLab V.rank V.rank) {z} ∧ SphOp V P (d.map fun x => x - 1) (R.image (· * z)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, hRs, hc⟩ := hR
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hzc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hzc k hk.2
  have sh : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := sh (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero, Finset.image_singleton, one_mul] at S0
  refine ⟨z, fun γ hγ => hzc γ (hRs γ hγ), S0, sh hα hD hRs hc ?_⟩
  exact List.pairwise_map.2 (hd.imp fun h => by omega)

theorem isLab_of_shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ}
    (h : IsLab V P (d.map fun x => x - 1)) : IsLab V P d := by
  obtain ⟨R, e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, -, -⟩ := h
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, -, hz⟩ := exists_central he.1 V h0
  have D1 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).1
  have D2 := divAt_mul h0 hz D1
  have D3 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 D2).1
  rw [dual_shift] at D3
  refine GlobalTheory.SphLabelOps.isLab_of_divAt hpi h1 h2 ?_ ?_ D3
  · exact (List.pairwise_map.1 hd).imp fun h => by omega
  · exact suppAt_inv (suppAt_mul (suppAt_inv hα) hs)

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  classical
  intro D V P hP d M _ _ π u hu
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  by_cases hl : IsLab V P d
  · obtain ⟨z, hzR, S0, S1⟩ := shift hP (GlobalTheory.SphLabelOps.sphOp_rep hl)
    have fw := (GlobalTheory.SphLabelOps.label_operators V P).2.1 (Finsupp.single d 1) M π u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (c1 _ _ S0).2 M π _ fw, ← (c1 _ _ S1).2 M π u hu, Finset.sum_singleton, GlobalTheory.SphLabelOps.opOf_single,
      map_sum, Finset.sum_image (mul_left_injective z).injOn]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hzR γ hγ, map_mul, Module.End.mul_apply]
  · have hl' : ¬ IsLab V P (d.map fun x => x - 1) := fun h => hl (isLab_of_shift hP h)
    have e0 : rep V P d = ∅ := by rw [Hk3.rep, dite_eq_right hl]
    have e1 : rep V P (d.map fun x => x - 1) = ∅ := by rw [Hk3.rep, dite_eq_right hl']
    rw [GlobalTheory.SphLabelOps.opOf_single π d, e0, Finset.sum_empty, map_zero, GlobalTheory.SphLabelOps.opOf_single, e1,
      Finset.sum_empty]

end GlobalTheory.CentralShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHecke_scalarLabel_comp_eq_shiftDown_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  first | exact @GlobalTheory.CentralShift.central_shift | exact GlobalTheory.CentralShift.central_shift | (intros; apply GlobalTheory.CentralShift.central_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_mul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (z : L) :
    ∃ n : ℕ, Valued.v (ϖ ^ n * z) ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hv).symm⟩
  refine ⟨m.toNat, ?_⟩
  rw [map_mul, map_pow, hϖ, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]
  have := Int.self_le_toNat m
  omega

theorem pow_mul_int_mono {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) {z : L} {n m : ℕ} (hnm : n ≤ m)
    (h : Valued.v (ϖ ^ n * z) ≤ 1) : Valued.v (ϖ ^ m * z) ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm (ϖ ^ n), mul_assoc, map_mul, map_pow]
  exact mul_le_one' (pow_le_one' hϖ k) h

theorem exists_pow_smul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) : ∃ K : ℕ, ∀ i j, Valued.v (ϖ ^ K * x i j) ≤ 1 := by
  choose n hn using fun p : Fin a × Fin b => exists_pow_mul_int hϖ (x p.1 p.2)
  have hϖ1 : Valued.v ϖ ≤ 1 := by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  refine ⟨∑ p, n p, fun i j => pow_mul_int_mono hϖ1 ?_ (hn (i, j))⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))

theorem finite_range_latIdx {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) :
    (Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a)).Finite := by
  obtain ⟨-, -, -, hϖ, -, h2q, hc⟩ := hU
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : V ϖ ≤ 1 := by rw [hV, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hc' : Nat.card (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) = q ^ 2 := hc
  haveI : Finite (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ (by omega))
  let ϖO : V.valuationSubring := ⟨ϖ, hϖ1⟩
  have hmax : IsLocalRing.maximalIdeal V.valuationSubring ≤ Ideal.span {ϖO} := by
    intro z hz
    rw [Valuation.mem_maximalIdeal_iff] at hz
    rw [Ideal.mem_span_singleton']
    by_cases hz0 : (z : L) = 0
    · exact ⟨0, by ext; simp [hz0]⟩
    have hϖ0 : ϖ ≠ 0 := by
      intro e; rw [e, map_zero] at hϖ'; exact WithZero.zero_ne_coe hϖ'
    have hz' : Valued.v (z : L) < 1 := hz
    have hle : Valued.v (z : L) ≤ Valued.v ϖ := by
      have hv : Valued.v (z : L) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
      rw [hϖ', ← WithZero.exp_log hv, WithZero.exp_le_exp]
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz'
      omega
    have hq1 : Valued.v ((z : L) / ϖ) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (by rw [hϖ']; exact WithZero.exp_pos)]
      exact hle
    refine ⟨⟨(z : L) / ϖ, hq1⟩, ?_⟩
    ext
    simp [ϖO, div_mul_cancel₀ _ hϖ0]
  haveI : Finite (V.valuationSubring ⧸ Ideal.span {ϖO}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hmax)
  obtain ⟨K, hK⟩ := exists_pow_smul_int hϖ' x
  haveI hfinK : Finite (V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) :=
    Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) K
  let g : (Fin b → V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) → (Fin a → L) ⧸ intVec L a :=
    fun c => QuotientAddGroup.mk (Matrix.mulVec x fun j => (((c j).out : V.valuationSubring) : L))
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨u, rfl⟩
  have hu : ∀ j, Valued.v ((u : Fin b → L) j) ≤ 1 := (mem_intVec _).1 u.2
  refine ⟨fun j => Ideal.Quotient.mk _ ⟨(u : Fin b → L) j, hu j⟩, ?_⟩
  have hd : ∀ j, ∃ t : V.valuationSubring,
      (((Ideal.Quotient.mk (Ideal.span {ϖO} ^ K) ⟨(u : Fin b → L) j, hu j⟩).out : V.valuationSubring) : L) =
        (u : Fin b → L) j + ϖ ^ K * t := by
    intro j
    have hm := Ideal.Quotient.mk_out (I := Ideal.span {ϖO} ^ K)
      (⟨(u : Fin b → L) j, hu j⟩ : V.valuationSubring)
    have hm' := Ideal.Quotient.eq.1 hm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((Ideal.span_singleton_pow ϖO K).le hm')
    refine ⟨t, ?_⟩
    have := congrArg (fun w : V.valuationSubring => (w : L)) ht
    push_cast at this
    simp only [ϖO] at this
    linear_combination -this
  choose t ht using hd
  refine (QuotientAddGroup.eq.2 ?_).symm
  intro i
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, ht, mul_add, Finset.sum_add_distrib,
    neg_add_cancel_left]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [show x i j * (ϖ ^ K * (t j : L)) = (ϖ ^ K * x i j) * (t j : L) by ring]
  exact Subring.mul_mem _ (hK i j) (t j).2

theorem latIdx_le_of_ker : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) →
      ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  intro L _ _ ϖ σ q a b x y hU hN
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSx
  set Sy := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec y (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSy
  let h : (Fin a → L) ⧸ intVec L a → (Fin a → L) ⧸ intVec L a := fun c =>
    if hc : ∃ u : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = c
    then QuotientAddGroup.mk (Matrix.mulVec y (hc.choose : Fin b → L)) else 0
  have hsub : Sy ⊆ h '' Sx := by
    rintro _ ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    have hc : ∃ u' : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u' : Fin b → L)) : (Fin a → L) ⧸ intVec L a) =
        QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) := ⟨u, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he ⊢
    have hd := hN ((u : Fin b → L) - (u' : Fin b → L)) (fun i => Subring.sub_mem _ (u.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  unfold latIdx
  rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (hfin.image h)).trans (Set.ncard_image_le hfin)

end GlobalTheory.Hk3.HoweDuality

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernelStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) → ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | exact GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker <;> assumption)
end
end

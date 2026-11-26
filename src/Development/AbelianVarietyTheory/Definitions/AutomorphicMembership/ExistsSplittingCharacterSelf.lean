module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyBesselPeriodPositionOneData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Host Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AntiChar

theorem exists_split_place (R : Ranks) (H : Formalism.BasicNotions.Host R) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), ¬ GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w ∧
      ∃ p : ℕ, p.Prime ∧ Units.torsionOrder H.E + 1 < p ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
  obtain ⟨p, hp, hp2, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := H.QS * H.q * H.d) (Units.torsionOrder H.E + 1) H.condN_ne_zero
  have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p hp hmod
  have hne : {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hs]
    exact Module.finrank_pos.ne'
  obtain ⟨w, hw⟩ := hne
  obtain ⟨-, -, ⟨x, hx, hx'⟩, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs w hw
  refine ⟨w, fun h => ?_, p, hp, hp2, hw⟩
  · have h' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w).2 h
    let y : 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv x
    exact hx' y rfl ((h' x y rfl).1 hx)

theorem exists_hchar (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (e : I ≃ R.Psi) (z : I → ℤ) :
    ∃ χ : HChar H.E, χ.IsUnitary ∧ χ.TrivOn H.F ∧ χ.HasInf (fun i => embPsi H (e i)) (fun i => -2 * z i) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 H.E)), ∀ v, v ∉ T → χ.UnrAt v := by
  classical
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hcm' : GlobalTheory.Mem.Chr.CMData H.F c (fun i => embPsi H (e i)) :=
    ⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp e.bijective⟩
  obtain ⟨w, hw, p, hp, hp2, hpw⟩ := exists_split_place R H
  rw [← hce] at hw
  obtain ⟨ω, -, hω⟩ := UpperTheory.Mu.tame_par w hp hp2 hpw (fun i => embPsi H (e i)) (fun i => -z i)
  obtain ⟨w', -, hw'⟩ := GlobalTheory.Mem.Chr.conjPl_main.1 H.E c.toRingEquiv w
  let θ0 : ∀ v : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ v.asIdeal)ˣ →* ℂˣ :=
    Function.update (fun _ => 1) w ω
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ := GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c I _ hcm' z {w} θ0
    (by
      intro v hv v' h hv'
      rw [Finset.mem_singleton] at hv hv'
      subst hv hv'
      exact hw h)
    (fun ζ hζ => by
      rw [Finset.prod_singleton]
      simp only [θ0, Function.update_self]
      exact hω ζ hζ)
  refine ⟨χ, hu, ht, hi, {w, w'}, fun v hv => hunr v ?_ ?_⟩
  · intro h
    exact hv (by rw [Finset.mem_singleton.1 h]; simp)
  · intro u hu' h
    rw [Finset.mem_singleton.1 hu'] at h
    exact hv (by rw [hw' v h]; simp)

theorem val_fin_principal (D : D7) (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (k : D.host.Eˣ) (x : (AE D)ˣ)
    (h1 : infPart D (x : AE D) = 1) (h2 : finPart D (x : AE D) = finPart D (incA D k)) :
    ((χ.inf k : ℂˣ) : ℂ) * ((c x : Circle) : ℂ) = 1 := by
  classical
  obtain ⟨ι, i1, i2, i3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι i1 i2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι i1 i2 i3) c χ hc
  obtain ⟨S, -, -, hS⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom k)
  have hx : ∀ P, ι (finPart D (x : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) k := fun P => by
    rw [h2]
    exact congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y P) (i1 k)
  have hS' : ∀ P, P ∉ S ∪ T → P.valuation D.host.E (k : D.host.E) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := fun P hP => by
    have := hS P fun h => hP (Finset.mem_union_left _ h)
    exact ⟨(GlobalTheory.BaseIdeleTriv.val_algebraMap P (k : D.host.E)).symm.trans this.1, this.2⟩
  have h3 := hprod x h1 (S ∪ T) (fun _ => k)
    (fun P _ => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap], by rw [hx, sub_self, map_zero]; exact zero_le⟩)
    (fun P hP => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap]; exact (hS' P hP).1, (hS' P hP).2⟩)
  have h4 := GlobalTheory.HeckeProduct.hchar_productRule D.host.E χ (S ∪ T)
    (fun v hv => hT v fun h => hv (Finset.mem_union_right _ h)) k
  have h5 : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S ∪ T), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => (finprod_congr fun hv => by
      show χ.val v ^ ordF v k = 1
      rw [ordF, (hS' v hv).1]; simp).trans finprod_one
  rw [h5, mul_one] at h4
  rw [h3, ← Units.coe_prod, ← Units.val_mul, h4, Units.val_one]


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in
theorem val_inf (D : D7) [Fintype D.what₂.Tau] (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (n : D.what₂.Tau → ℤ)
    (hn : χ.HasInf (tauE D) n) (θ : InfF D) (hθ : IsInfFam θ) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  obtain ⟨s, hs⟩ := GlobalTheory.FockCompare.exists_chart hθ
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let U : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Uc : Continuous U.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hU : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 →
      y = U.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y := fun y hy =>
    Units.ext (ext _ _ (hy.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ, ((c (U.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n τ := by
    intro z
    refine (GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z
      (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Uc)) ?_) fun k => ?_
    · refine continuous_finsetProd _ fun τ _ => ?_
      have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h3 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0 := fun z => by
        exact_mod_cast norm_ne_zero_iff.2 (z τ).ne_zero
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun z => Or.inl (div_ne_zero (z τ).ne_zero (h3 z))
    · let y : (AE D)ˣ := Units.map (incA D).toMonoidHom k
      have e1 : a y = U.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k := by
        rw [hU (a y) (ha y).2]
        congr 1
        funext τ
        exact Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))
      have e2 := val_fin_principal D c χ hc T hT k (b y) (hb y).1 (hb y).2
      have e3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 k
      have e4 : ((c (a y) : Circle) : ℂ) * ((c (b y) : Circle) : ℂ) = 1 := by rw [← Circle.coe_mul, e3, Circle.coe_one]
      rw [← e1]
      exact (mul_right_cancel₀ (Circle.coe_ne_zero _) (e4.trans e2.symm)).trans (hn k)
  exact (congrArg (fun y => ((c y : Circle) : ℂ)) (hU x hx)).trans (key _)

theorem sign_zpow_even {w : ℂ} (hw : starRingEnd ℂ w = w) (h0 : w ≠ 0) (m : ℤ) : (w / (‖w‖ : ℂ)) ^ (-2 * m) = 1 := by
  have h1 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have h2 : (w / (‖w‖ : ℂ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', hw, sq]
    exact div_self (mul_ne_zero h0 h0)
  rw [show -2 * m = 2 * -m by ring, _root_.zpow_mul, h2, _root_.one_zpow]


set_option maxHeartbeats 1000000 in
theorem exists_char : ∀ (D : D7) (j : Fin D.R.m),
    ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (-(D.hc τ).e j)) ∧ ResEta D χ 0 := by
  intro D j
  classical
  letI : Fintype D.what₂.Tau := Fintype.ofEquiv _ D.eTau.symm
  choose z hz using fun τ => (D.hc τ).e_int j
  obtain ⟨χ, hu, ht, hi, T, hT⟩ := exists_hchar D.R D.host D.what₂.Tau D.eTau z
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D χ hu
  have hv := val_inf D c χ hc T hT _ hi
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.Member.exists_isInfFam_family D
  refine ⟨c, hc.1, fun τ => ⟨-2 * z τ, by rw [hz]; push_cast; ring, ⟨θ₀, hθ₀⟩, fun θ hθ x h1 h2 => ?_⟩,
    GlobalTheory.VolHeckeCompare.exists_isEta D, fun η _ a => ?_⟩
  · rw [hv θ hθ x h1, Finset.prod_eq_single τ (fun τ' _ h => by rw [h2 τ' h]; simp) (by simp)]
  · let p : AF D.host.F →* AF D.host.F := (MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))
    let q : AF D.host.F →* AF D.host.F := (MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))
    have e : a = Units.map p a * Units.map q a := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have e1 : c (idF D (Units.map q a)) = 1 := GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc ht _ rfl
    have e2 : c (idF D (Units.map p a)) = 1 := by
      apply Circle.ext
      rw [hv θ₀ hθ₀ _ rfl, Circle.coe_one]
      refine Finset.prod_eq_one fun τ _ => sign_zpow_even (GlobalTheory.FockCompare.conj_tmul_one hθ₀ τ _) ?_ _
      exact (Units.map ((θ₀ τ).comp (infPart D)).toMonoidHom (idF D (Units.map p a))).ne_zero
    rw [pow_zero, e, map_mul, map_mul, e1, e2, one_mul]

end GlobalTheory.Mem.AntiChar
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitFacTwistRight
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.ThModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem orthEx (D : D7) : OrthEx D := by
  intro V hV
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (two_ne_zero : (2 : D.host.E) ≠ 0) V.rank V.hT.flip
    (fun x y => V.herm.eq y x) V.rank_eq
  have ho : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0 := fun i j hij => hb j i hij.symm
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.FockBasisMatrix.basis_matrix D V).2 b
  have hd : ∀ τ, ((V.frame.toMatrix b).map (tauE D τ)).det ≠ 0 := fun τ => by
    have := (tauE D τ).map_det (V.frame.toMatrix b)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (h1.map (tauE D τ)).ne_zero
  choose A hA hA' using fun τ => GlobalTheory.MonomialDiag.exists_monomial _ _ _ (gramAt D V τ) _ _ (hV (tauE D τ)) (hd τ)
    (h3 ho τ).1 (h3 ho τ).2.1
  exact ⟨A, V.frame.toMatrix b, hA, h1, fun i j hij => (h2 i j).trans (ho i j hij), hA'⟩

theorem nonempty_orthDec (D : D7) : Nonempty (OrthDec D) := GlobalTheory.Mem.Th.nonempty_orthDec (orthEx D)

end GlobalTheory.Mem.ThModel

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AdmE (V W : HSp D) (χ χ' : IdC D) : Prop :=
  V.rank = W.rank ∧ IsHC D χ ∧ IsHC D χ' ∧ ResEta D χ V.rank ∧ ResEta D χ' W.rank

theorem IsHC.mul {χ ν : IdC D} (h : IsHC D χ) (k : IsHC D ν) : IsHC D (χ * ν) :=
  ⟨⟨h.1.1.mul k.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, k.1.2, mul_one]⟩, fun τ =>
    (h.2 τ).elim fun _ ha => (k.2 τ).elim fun _ hb => ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul ha hb⟩⟩

structure WeilFun.EqRank {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) : Prop where
  weil : ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → IsWeilOn ψ V W χ χ' (Wf.om V W χ χ')
  twW : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot V g x →
    Wf.om V W χ (χ' * ν) (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • Wf.om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot W h x →
    Wf.om V W (χ * ν) χ' (g, h) = ((ν x : Circle) : ℂ) • Wf.om V W χ χ' (g, h)

def WeilOnEqEx (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → ∃ om, IsWeilOn ψ V W χ χ' om

def WeilTwEq (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 →
  ∀ om, IsWeilOn ψ V W χ χ' om →
    (∀ om', IsWeilOn ψ V W χ (χ' * ν) om' → ∀ g h x, IsDetRoot V g x → om' (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • om (g, h)) ∧
    ∀ om', IsWeilOn ψ V W (χ * ν) χ' om' → ∀ g h x, IsDetRoot W h x → om' (g, h) = ((ν x : Circle) : ℂ) • om (g, h)


def LiftAutEq (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' →
  ∀ om, IsWeilOn ψ V W χ χ' om → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ (Φ : ThS ψ V W) F, IsCuspForm θ V F →
    (∀ h, IntegrableOn (fun g => (om (g, h) Φ).1 0 * F g) 𝓕 μ) ∧
    IsAutFunSm θ W fun h => ∫ g in 𝓕, (om (g, h) Φ).1 0 * F g ∂μ

structure RealisesE {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} (B : BesselTied D X T W)
    (Wf : WeilFun D W.ψ) (Tw : Tow D) (Rc : RecFun D θ W.ψ) : Prop where
  inf : IsInfFam θ

  eqRank : Wf.EqRank := by assumption

  forms : ∀ V, Set.range (T.ev V) = {φ | IsAutFunSm θ V φ}
  typ : ∀ V P F, F ∈ X.typ V P ↔ T.ev V F ∈ TypS θ V P

  sch : ∀ V V', Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  chr : ∀ μ j, T.eChr (X.chrOf μ j) = Rc.chr μ j
  eta : T.eChr X.etaT = Rc.eta
  col : ∀ u μ j φ, T.ev _ (X.colAF u μ j φ).1 = (Rc.col u μ j φ).1
  row : ∀ μ j F, T.ev _ (X.rowAF μ j F).1 = (Rc.row μ j F).1
  phi : ∀ μ j, W.evS _ _ (X.PhiY μ j) = (Rc.Phi μ j).1
  phiUp : PhiYupTied W
  mY : X.mY = Rc.mY
  petF : T.petF = Rc.petF
  petR : T.petR = Rc.meas.petR
  xs : X.Xs = Tw.Xs
  ys : X.Ys = Tw.Ys
  ysLow : X.YsLow = Tw.YsLow
  iXYs : ∀ t j, HEq (X.iXYs t j) (Tw.iXYs t j)
  iYXm : ∀ t, HEq (X.iYXm t) (Tw.iYXm t)
  om : ∀ V V' χ χ' p (Φ : X.Sch V V') (f : ThS W.ψ V V'), W.evS V V' Φ = f.1 →
    W.evS V V' (W.om V V' χ χ' p Φ) = (Wf.om V V' (T.eChr χ) (T.eChr χ') p f).1

  thOff : ∀ (V V' : HSp D) χ χ', ¬ ((admitted V V' (T.eChr χ) (T.eChr χ') ∨ AdmE V V' (T.eChr χ) (T.eChr χ')) ∧ V.SigOK) →
    X.th V V' χ χ' = 0

  thEq : ∀ (V V' : HSp D) χ χ', AdmE V V' (T.eChr χ) (T.eChr χ') → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'), T.ev V' (X.th V V' χ χ' Φ F) h =
      (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

  fact : ∀ V V' Φ, Φ ∈ X.fact V V' ↔ IsPureFun W.ψ V V' (W.evS V V' Φ)

  kfin : ∃ K : KfinTied W, K.cpt = Rc.dec.cpt ∧ K.bas = Rc.dec.bas

  posDat : ∀ u ho, B.dat _ _ _ ho (X.posSym u) = Rc.posSym u ∧ B.dat _ _ _ ho (X.pos1 u) = Rc.pos1 u

  pos1Val : ∀ u σ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 → ∀ ν 𝓝, (Rc.per1.dat u).bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), X.Bper _ _ _ (X.pos1 u) σ φ F = (T.petC (D.sp.X 0) : ℂ) *
      (Rc.per1.dat u).period W.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev _ φ g)) (T.ev _ (F : X.AF (D.sp.Y 0)))

  besAll : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ d : BesDat A A' ι, (d.y : GA D A') = 1 → ∃ p, B.dat A A' ι ho p = d ∧ BesGlob T W.ψ d p

  besOnly : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ p, BesGlob T W.ψ (B.dat A A' ι ho p) p ∨ ∃ u,
      (⟨A, A', ι, p⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι) = ⟨_, _, _, X.pos1 u⟩

def RealisedExE (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ Wf : WeilFun D ψ, Wf.EqRank → ∀ (Tw : Tow D) (Rc : RecFun D θ ψ),
    ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T) (B : BesselTied D X T W) (h : W.ψ = ψ),
      RealisesE (θ := θ) B (h ▸ Wf) Tw (h ▸ Rc)

section Lift

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ}


end Lift

structure WeilThetaCompatibility {X : ThetaX D} {T : ThetaTied D X} (W : WeilTied D X T) : Prop where
  range : ∀ V V' : HSp D, V.rank = V'.rank → Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  Heisenberg₂ : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ g h w₀ Φ Φ', W.evS V V' Φ' = Heisenberg₂ W.ψ V V' w₀ (W.evS V V' Φ) →
      W.evS V V' (W.om V V' χ χ' (g, h) Φ') =
        Formalism.L2.Theta.Heisenberg₂ W.ψ V V' (actHom V V' g h w₀) (W.evS V V' (W.om V V' χ χ' (g, h) Φ))
  aut : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ V', ∀ Φ, W.evS V V' (W.om V V' χ χ' (γ, γ') Φ) 0 = W.evS V V' Φ 0
  cont : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D V' => W.evS V V' (W.om V V' χ χ' p Φ) w
  unit : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ (μ : Measure (WA V V')) (𝓕 : Set (WA V V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V V') 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖W.evS V V' (W.om V V' χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖W.evS V V' Φ w‖ ^ 2 ∂μ
  split : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e V' h → ∀ x y, IsDetAt e V g x → IsDetAt e V' h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V V' →ₗ[ℂ] ℂ,
      (∀ u : WA V V', (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ',
        W.evS V V' Φ' = Formalism.L2.Theta.Heisenberg₂ W.ψ V V' u (W.evS V V' Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (W.om V V' χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V V' (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ
  twW : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      W.om V V' χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  twV : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V' h x →
      W.om V V' (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  th : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'),
      T.ev V' (X.th V V' χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

namespace RealisesE

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc)

include h

theorem eq_of_isInfFam {θ' : InfF D} (h' : IsInfFam θ') : θ' = θ :=
  ((GlobalTheory.AutFunCompare.isInfFam_iff θ').1 h').trans ((GlobalTheory.AutFunCompare.isInfFam_iff θ).1 h.inf).symm

theorem afTiedSm : ThetaSmoothnessCondition T := ⟨⟨θ, h.inf⟩, fun _ h' V _ => by rw [h.eq_of_isInfFam h']; exact h.forms V⟩

theorem formSub : FormSub D := fun θ' h' V φ => by
  rw [h.eq_of_isInfFam h']
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  have : AFs θ V ≤ LinearMap.range (T.ev V) := Submodule.span_le.2 (by rw [LinearMap.coe_range, h.forms V])
  have h2 : φ ∈ Set.range (T.ev V) := this hφ
  rwa [h.forms V] at h2

theorem typTied (ht : TypAdd D) : TypTied T := ⟨⟨θ, h.inf⟩, fun _ h' V hV P hP => by
  intros
  rename_i F
  rw [h.eq_of_isInfFam h', h.typ, mem_TypS h.formSub ht h.inf hV hP]
  have : T.ev V F ∈ Set.range (T.ev V) := ⟨F, rfl⟩
  rw [h.forms V] at this
  exact ⟨fun k => k.2, fun k => ⟨this, k⟩⟩⟩

theorem weilUnrTied : WeilUnramifiedCondition W := fun V V' χ χ' hr h1 h2 S u1 u2 k hk k' hk' Φ hΦ => by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
  rw [h.sch] at hf
  refine W.evS_inj V V' ?_
  rw [h.om V V' χ χ' (k, k') Φ ⟨_, mem_ThS.2 hf⟩ rfl,
    Wf.om_unr V V' _ _ ⟨hr, hc χ, hc χ', h1, h2⟩ S u1 u2 k hk k' hk' _ hΦ]

def schEquiv (V V' : HSp D) : X.Sch V V' ≃ₗ[ℂ] ThS W.ψ V V' :=
  LinearEquiv.ofBijective ((W.evS V V').codRestrict _ fun Φ => mem_ThS.2 (by
      have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
      rwa [h.sch] at hf))
    ⟨fun _ _ e => W.evS_inj V V' (congrArg Subtype.val e), fun f => by
      have hf : f.1 ∈ Set.range (W.evS V V') := by rw [h.sch]; exact mem_ThS.1 f.2
      exact hf.imp fun _ e => Subtype.ext e⟩

theorem schEquiv_om (V V' : HSp D) (χ χ') (p) (Φ : X.Sch V V') :
    h.schEquiv V V' (W.om V V' χ χ' p Φ) = Wf.om V V' (T.eChr χ) (T.eChr χ') p (h.schEquiv V V' Φ) :=
  Subtype.ext (h.om V V' χ χ' p Φ _ rfl)

theorem eqTied : WeilThetaCompatibility W := by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have ha : ∀ {V V' : HSp D} {χ χ'}, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
      AdmE V V' (T.eChr χ) (T.eChr χ') := fun hr h1 h2 => ⟨hr, hc _, hc _, h1, h2⟩
  have ho := fun V V' χ χ' p Φ => h.om V V' χ χ' p Φ (h.schEquiv V V' Φ) rfl
  refine ⟨fun V V' _ => h.sch V V', fun V V' χ χ' hr h1 h2 g x w₀ Φ Φ' e => ?_, fun V V' χ χ' hr h1 h2 γ hγ γ' hγ' Φ => ?_,
    fun V V' χ χ' hr h1 h2 Φ w => ?_, fun V V' χ χ' hr h1 h2 μ 𝓕 hμ h𝓕 p Φ => ?_,
    fun V V' χ χ' hr h1 h2 e he g x hg hx a b k1 k2 => ?_, fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_,
    fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_, fun V V' χ χ' hr h1 h2 => h.thEq V V' χ χ' (ha hr h1 h2)⟩
  · rw [ho, ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).Heisenberg₂ g x w₀ _ _ e
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).aut γ hγ γ' hγ' _
  · simp only [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).cont _ w
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).unit μ 𝓕 hμ h𝓕 p _
  · obtain ⟨r, hr0, k⟩ := (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).split e he g x hg hx a b k1 k2
    refine ⟨r, hr0, fun ℓ hℓ Φ => ?_⟩
    have := k (ℓ ∘ₗ (h.schEquiv V V').symm.toLinearMap) (fun u hu f f' e' => by
      obtain ⟨Ψ, rfl⟩ := (h.schEquiv V V').surjective f
      obtain ⟨Ψ', rfl⟩ := (h.schEquiv V V').surjective f'
      simpa using hℓ u hu Ψ Ψ' e') (h.schEquiv V V' Φ)
    rw [← h.schEquiv_om] at this
    simpa using this
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twW _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twV _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]

theorem petC_eq (V : HSp D) : T.petC V = Rc.petC V := by
  unfold ThetaTied.petC RecFun.petC; rw [h.petF, h.petR]

theorem carY_eq (μ s i) : T.eChr (X.carY μ s i) = Rc.carY μ s i := by
  unfold ThetaX.carY RecFun.carY
  split_ifs
  · rw [map_mul, map_inv, h.chr, h.eta]
  · exact h.chr _ _

theorem tieIo (hi : Rc.IoTie Wf) : X.TieIo := fun μ j hj y x => by
  obtain ⟨L, hL, hx⟩ := hi μ j hj y
  obtain ⟨⟨m, hm⟩, h2⟩ := hx x
  have e : T.ev _ (X.dnY μ j (X.rowAF μ (j + 1) y)) = L := by
    funext g
    obtain ⟨⟨n, hn⟩, h3⟩ := hL g
    have k := W.th _ _ _ _ (rank_Y_ne X j hj) (row_lift_ok T μ (j + 1) (by omega) hj (j + 1) hj)
      (row_lift_ok T μ (j + 1) (by omega) hj j hj.le) (D.sp.Y_sig _) n.1 n.2 hn (X.PhiY μ j) (X.rowAF μ (j + 1) y) g
    unfold ThetaX.dnY
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, k, (h3 n hn).2]
    simp only [h.om _ _ _ _ _ _ _ (h.phi μ j), h.carY_eq, h.row, h.mY, ← h.petC_eq, WeilFun.ker, Complex.ofReal_mul,
      mul_assoc, smul_eq_mul]
  unfold ThetaX.petY
  rw [T.pet _ (D.sp.Y_sig j) m.1 m.2 hm, (h2 m hm).2, e, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

end RealisesE

structure ChrRead {X : ThetaX D} (T : ThetaTied D X) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (T.eChr (X.chrOf μ (j.1 + 1))) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq (T.eChr X.etaT) C.eta

structure RecFun.ChrIs {θ : InfF D} {ψ : AddChar (AF D.host.F) ℂ} (Rc : RecFun D θ ψ) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Rc.chr μ (j.1 + 1)) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq Rc.eta C.eta


open Formalism.IndefR.Links in
theorem RecFun.exists_chrIs (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) (ht : ∀ μ, (xi μ).TrivOn D.host.F) (θ : InfF D)
    (ψ : AddChar (AF D.host.F) ℂ) : ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi := by
  choose n hn ho using hf
  choose m hm using fun j => GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  choose x hx using fun μ => GlobalTheory.CharTransport.exists_chrEq D (xi μ) (Formalism.L2.Host.HChar.isUnitary_of_order (hn μ) (ho μ))
  obtain ⟨η, hη⟩ := GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D η C.eta hη C.isEta
  obtain ⟨P⟩ := GlobalTheory.PosOneData.nonempty_besselPeriodPositionOneData D
  obtain ⟨Dc⟩ := GlobalTheory.Mem.ThModel.nonempty_orthDec D
  obtain ⟨R⟩ := nonempty_recFun θ ψ (GlobalTheory.Mem.AntiChar.exists_char D) (GlobalTheory.Mem.EtaTilde.exists_etaTilde D)
    (GlobalTheory.Mem.ThetaNonzero.exists_thetaFun_ne_zero D ψ) Dc P
  have h2 := D.R.two_le_m
  have hexp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (m j * x μ) τ (-(D.hc τ).e j) := fun μ j τ => by
    have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hm j)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (C.isMu0 j).inf) τ)
      (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hx μ) (hn μ) (ho μ) τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have heq : ∀ μ j, ChrEq (m j * x μ) (C.mu0 j * xi μ) := fun μ j =>
    ⟨⟨(hm j).1.1.mul (hx μ).1.1, fun y => by rw [MonoidHom.mul_apply, (hm j).1.2, (hx μ).1.2, mul_one]⟩,
      fun P e he k y hy => by
        rw [MonoidHom.mul_apply, Circle.coe_mul, (hm j).2 P e he k y hy, (hx μ).2 P e he k y hy, ← Units.val_mul]; rfl⟩
  have e : ∀ j : Fin D.R.m, (⟨(j.1 + 1 - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ : Fin D.R.m) = j := fun j =>
    Fin.ext (by simp [Nat.mod_eq_of_lt j.2])
  refine ⟨{ R with
    chr := fun μ j => m ⟨(j - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ * x μ
    chr_hc := fun μ _ => ⟨(heq μ _).1, fun τ => ⟨_, hexp μ _ τ⟩⟩
    chr_inf := fun μ j τ => by rw [e]; exact hexp μ j τ
    chr_res := fun μ _ _ _ => ⟨⟨_, hres⟩, fun η' _ a => by
      rw [pow_zero, MonoidHom.mul_apply, GlobalTheory.GridWeil.triv_base (hm _) (C.isMu0 _).triv a,
        GlobalTheory.GridWeil.triv_base (hx μ) (ht μ) a, mul_one]⟩
    eta := η, eta_hc := hη.1
    eta_inf := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, C.isEta.inf⟩)
    eta_res := ⟨⟨_, hres⟩, fun η' hη' a => by
      rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' hres, pow_one, MonoidHom.comp_apply]⟩
    eta_unr := GlobalTheory.EtaConjExist.unram_of_chrEq hη C.isEta.unr }, fun μ j => ?_, hη⟩
  show ChrEq (m _ * x μ) _
  rw [e]; exact heq μ j

theorem RealisesE.chrRead {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
    {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc) {C : Formalism.L2.Host.CharFrame D}
    {xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E} (k : Rc.ChrIs C xi) : ChrRead T C xi :=
  ⟨fun μ j => by rw [h.chr]; exact k.chr μ j, by rw [h.eta]; exact k.eta⟩

end GlobalTheory.Mem.Th

end

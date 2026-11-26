module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per

namespace UpperTheory.Gal.crystallineComparison

def AffFinProj : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f → AffFin Y

theorem heckePol_map {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (q n : ℕ) (θ : ℕ → K) :
    (heckePol q n θ).map f = heckePol q n fun j => f (θ j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [heckePol, Polynomial.map_sum]

def AdmOfCrys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ

theorem admissible_of_crystalline : AdmOfCrys := by
  intro l _ P K V _ _ ρ h
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted
  rw [e]
  exact h

end UpperTheory.Gal.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PUnrGeom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.unrGeom_of :
    UnrOfGeom := by
  classical
  intro E Ω _ _ _ _ _ A w h x y hx hy g hg hxy
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hx
  obtain ⟨m, d, rfl⟩ := Unram.exists_diag hy
  rw [WD.charPol_mk, WD.charPol_mk, WDRep.diag_ρ, WDRep.diag_ρ, charpoly_diagEnd, charpoly_diagEnd, hg] at hxy
  have key := congrArg Polynomial.roots hxy
  simp only [Finset.prod_eq_multiset_prod] at key
  have R : ∀ {k : ℕ} (e : Fin k → ℂˣ),
      (Multiset.map (fun i => Polynomial.X - Polynomial.C (((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))) Finset.univ.val).prod.roots =
        Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ) := by
    intro k e
    have := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))
    rwa [Multiset.map_map] at this
  rw [R, R] at key
  apply Unram.diag_eq_diag
  have := congrArg (Multiset.map fun z : ℂ => z⁻¹) key
  simpa [Multiset.map_map, Function.comp_def, zpow_neg_one, inv_inv] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem charPol_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (LL : FinExt l)
    {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) (g : ↥(Weil h)) :
    haveI := hV.finite
    (wdPst P ι Bw h hj ρ).charPol g = (wdRho P ι Bw h hj ρ g).charpoly := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  exact (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq g

theorem UpperTheory.Gal.crystallineComparison.wdModel_of :
    WdModel := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hV g
  have key : wdAt P ι Bw h hj r = wdPst P ι Bw h hj (Bw.repE LL r') := by
    obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj (r := r) ⟨LL, r', hm, hV⟩
    have h₁ : L₁.1 ≤ (supExt L₁ LL).1 := le_sup_left
    have h₂ : LL.1 ≤ (supExt L₁ LL).1 := le_sup_right
    have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
        mapRep (IntermediateField.inclusion h₂).toRingHom r' := by
      ext x i j
      exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f x : Matrix (Fin a) (Fin a) (Om l)) i j)
        (hm₁.2.trans hm.2.symm)
    rw [e₁, GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₁ r₁ hV₁,
      GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₂ r' hV, e]
  refine ⟨?_, ?_⟩
  · rw [key]
    exact charPol_wdPst P ι h Bw hj LL (Bw.repE LL r') hV g
  · exact (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL _ _ hV).trans (by simp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSatGeom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem coe_bind (B : Multiset ℂˣ) :
    (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
  show B.bind (fun b => {(b : ℂ)}) = _
  exact Multiset.bind_singleton B _

theorem UpperTheory.Gal.crystallineComparison.satGeom_of :
    SatGeom := by
  intro E Ω _ _ _ _ _ A w h a B
  have h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)) := by
    simp
  refine ⟨?_, ?_⟩
  · show ((WD.lpUnr h _).lpTw _).unr
    rw [WD.unr_tw]
    exact (WD.lpUnr_spec _ h0).1
  intro g hg
  show ((WD.lpUnr h _).lpTw _).charPol g = _
  unfold WD.lpUnr
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]
  have hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i) := by
    intro s ι f
    ext v i
    simp [diagEnd, mul_assoc]
  rw [hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]
  set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs
  refine (congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)))
    (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_
  unfold rootPol
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro b _
  simp only [Function.comp_apply]
  have hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2) := by
    rw [hs, zpow_neg_one, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenScale
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftMap
theorem UpperTheory.Reformulated.B.Qk56.lift_map :
    ∀ {α β : Type} (f : α → β) (B : Multiset α)
    (t : Multiset β), (∀ x ∈ t, x ∈ Multiset.map f B) → ∃ (t' : Multiset α), Multiset.map f t' = t ∧ ∀ x ∈ t', x ∈ B := by
  intro α β f B t
  induction t using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, Multiset.map_zero f, fun x hx => absurd hx (Multiset.notMem_zero x)⟩
  | cons b s ih =>
    intro h
    obtain ⟨s', hs', hB⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    obtain ⟨a, ha, hab⟩ := Multiset.mem_map.1 (h b (Multiset.mem_cons_self b s))
    refine ⟨a ::ₘ s', by rw [Multiset.map_cons, hab, hs'], fun x hx => ?_⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hB x hx
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem prod_map_scale (z : ℂ) (s : Multiset ℂˣ) :
    (s.map fun b : ℂˣ => z * (b : ℂ)).prod = z ^ s.card * ((s.prod : ℂˣ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, Units.val_mul, pow_succ]
    ring

private theorem lift_map {α β : Type} (f : α → β) (B : Multiset α) (t : Multiset β)
    (h : ∀ x ∈ t, x ∈ B.map f) : ∃ t' : Multiset α, t'.map f = t ∧ ∀ x ∈ t', x ∈ B :=
  _root_.UpperTheory.Reformulated.B.Qk56.lift_map f B t h

private theorem generic_scale_units (B : Multiset ℂˣ) (z : ℂ) (hz : z ≠ 0) (hB : GenericMul B) :
    GenericMul (B.map fun b : ℂˣ => z * (b : ℂ)) := by
  intro t hc hm hp
  obtain ⟨t', rfl, h2⟩ := lift_map (fun b : ℂˣ => z * (b : ℂ)) B t hm
  have hcard : t'.card = B.card := by simpa using hc
  rw [prod_map_scale, prod_map_scale, hcard] at hp
  have hprod : t'.prod = B.prod :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero _ hz) hp)
  rw [hB t' hcard h2 hprod]

theorem UpperTheory.Gal.crystallineComparison.genScale_of :
    GenericScale := by
  intro B z hz hB
  have h := generic_scale_units B z hz hB
  have e : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton]
  rw [e, Multiset.map_map]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilWeil
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section Abstract

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

private theorem pow_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (m : ℕ) :
    (∀ s ∈ S, (Φ ^ m) s ∈ S) ∧ ∀ s (hs : s ∈ S), (((T ^ m) ⟨s, hSD hs⟩ : D) : M) = (Φ ^ m) s := by
  induction m with
  | zero => exact ⟨fun s hs => hs, fun s hs => rfl⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [pow_succ', End.mul_apply]
      exact hΦ _ (ih1 s hs)
    · rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply]
      have e : (T ^ m) ⟨s, hSD hs⟩ = ⟨(Φ ^ m) s, hSD (ih1 s hs)⟩ := Subtype.ext (ih2 s hs)
      rw [e, hT _ (ih1 s hs)]

private theorem aeval_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) :
    (∀ s ∈ S, Polynomial.aeval Φ Q s ∈ S) ∧
      ∀ s (hs : s ∈ S), ((Polynomial.aeval T Q ⟨s, hSD hs⟩ : D) : M) = Polynomial.aeval Φ Q s := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hp.1 s hs) (hq.1 s hs)
    · rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp.2 s hs, hq.2 s hs]
  | monomial n a =>
    obtain ⟨h1, h2⟩ := pow_restr D S hSD T Φ hΦ hT n
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [Polynomial.aeval_monomial, End.mul_apply, Module.algebraMap_end_apply]
      exact S.smul_mem a (h1 s hs)
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, h2 s hs]

private theorem aeval_commute {D : Type} [AddCommGroup D] [Module L D] (T m : End L D) (h : Commute T m)
    (Q : Polynomial L) : Commute (Polynomial.aeval T Q) m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (show Commute _ m from Algebra.commutes a m) (h.pow_left n)

private theorem nil_abs {U : Type} (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) (N : ℕ)
    (hN : ∀ s ∈ S, (Polynomial.aeval Φ Q ^ N) s = 0) (m : U → End L D) (mV : U → End L M)
    (hm : ∀ c (x : D), ((m c x : D) : M) = mV c x) (hc : ∀ c, T * m c = m c * T)
    (hcl : ∀ x : D, (x : M) ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s}) :
    IsNilpotent (Polynomial.aeval T Q) := by
  obtain ⟨a1, a2⟩ := aeval_restr D S hSD T Φ hΦ hT Q
  obtain ⟨-, b2⟩ := pow_restr D S hSD _ _ a1 a2 N
  have hkill : ∀ s (hs' : s ∈ S), (Polynomial.aeval T Q ^ N) ⟨s, hSD hs'⟩ = 0 := by
    intro s hs'
    refine Subtype.ext ?_
    rw [b2 s hs']
    exact hN s hs'
  have hcomm : ∀ c, Commute (Polynomial.aeval T Q ^ N) (m c) := fun c =>
    Commute.pow_left (aeval_commute _ _ (hc c) Q) N
  have key : ∀ y, y ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s} →
      ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0 := by
    intro y hy
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0)
      ?_ ⟨zero_mem _, map_zero _⟩ ?_ ?_ hy
    · rintro _ ⟨c, s, hs', rfl⟩
      have e : mV c s = ((m c ⟨s, hSD hs'⟩ : D) : M) := (hm c ⟨s, hSD hs'⟩).symm
      refine ⟨e ▸ (m c ⟨s, hSD hs'⟩).2, ?_⟩
      have h1 := LinearMap.congr_fun (hcomm c).eq ⟨s, hSD hs'⟩
      rw [End.mul_apply, End.mul_apply, hkill s hs', map_zero] at h1
      have h2 : (⟨mV c s, e ▸ (m c ⟨s, hSD hs'⟩).2⟩ : D) = m c ⟨s, hSD hs'⟩ := Subtype.ext e
      rw [h2]; exact h1
    · rintro a b _ _ ⟨ha, ea⟩ ⟨hb, eb⟩
      refine ⟨add_mem ha hb, ?_⟩
      have := map_add (Polynomial.aeval T Q ^ N) ⟨a, ha⟩ ⟨b, hb⟩
      rw [ea, eb, add_zero] at this
      exact this
    · rintro a _ ⟨ha, ea⟩
      refine ⟨neg_mem ha, ?_⟩
      have := map_neg (Polynomial.aeval T Q ^ N) ⟨a, ha⟩
      rw [ea, neg_zero] at this
      exact this
  refine ⟨N, LinearMap.ext fun x => ?_⟩
  obtain ⟨hy, e⟩ := key x.1 (hcl x)
  exact e

end Abstract

theorem UpperTheory.Gal.crystallineComparison.nilWeil_of :
    NilWeil := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV hs Q hN g hg
  haveI := hV.finite
  obtain ⟨N, hN⟩ := hN
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs =>
    (mem_Dpst P ρ).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P ρ).mp hs g⟩
  have hΦ : onPer (ψSt P (resDeg l w)) ↥LL.1 V = phiV P ↥LL.1 V ^ resDeg l w := by
    change onB P ↥LL.1 V ((phiSt P).toLinearMap ^ resDeg l w) = _
    rw [map_pow]; rfl
  have hpow : ∀ (m : ℕ) (x : ↥(Dpst P ρ)),
      (((phiD P ρ ^ m) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P ↥LL.1 V ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih]
  have hst : ∀ (m : ℕ), ∀ s ∈ Dst P ρ, (phiV P ↥LL.1 V ^ m) s ∈ Dst P ρ := by
    intro m s hs'
    refine (mem_Dst P ρ).mpr fun k => ?_
    have hc : Commute (phiV P ↥LL.1 V ^ m) (stRep P ρ k) := Commute.pow_left (phiV_stRep P ρ k) m
    have := LinearMap.congr_fun hc.eq s
    rw [End.mul_apply, End.mul_apply, (mem_Dst P ρ).mp hs' k] at this
    exact this.symm
  have hW : ∀ s (hs' : s ∈ Dst P ρ), ((weilD Bw h P ρ g ⟨s, hSD hs'⟩ : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      onPer (ψSt P (resDeg l w)) ↥LL.1 V s := by
    intro s hs'
    have e : -alpha l g = ((resDeg l w : ℕ) : ℤ) := by rw [alpha, hg]; ring
    rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD, hpow, hΦ]
    exact (mem_Dst P ρ).mp (hst _ s hs') _
  have hΦS : ∀ s ∈ Dst P ρ, onPer (ψSt P (resDeg l w)) ↥LL.1 V s ∈ Dst P ρ := by
    intro s hs'
    rw [hΦ]; exact hst _ s hs'
  have hcl := mem_closure_mulV_of_finrank_eq l P Bw.Kw LL V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun k => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ k c c (mem_GK.mp k.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx k]) hs
  exact nil_abs (Dpst P ρ) (Dst P ρ) hSD (weilD Bw h P ρ g) (onPer (ψSt P (resDeg l w)) ↥LL.1 V) hΦS hW Q N
    (fun s hs' => hN s hs') (mulD P ρ) (mulV P ↥LL.1 V) (fun _ _ => rfl) (weilD_mulD Bw h P ρ hj g) (fun x => hcl x.1 x.2)
end

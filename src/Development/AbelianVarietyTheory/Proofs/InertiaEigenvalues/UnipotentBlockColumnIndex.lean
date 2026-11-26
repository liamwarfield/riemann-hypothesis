module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep

namespace GlobalTheory.CuspGeneric

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

def IsCoLat (Γ : AddSubgroup G) : Prop :=
  DiscreteTopology Γ ∧ ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ γ ∈ Γ, γ + x ∈ K

def Per (Γ : AddSubgroup G) (Φ : G → ℂ) : Prop := Continuous Φ ∧ ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x


open Classical in
def avg (Γ : AddSubgroup G) (Φ : G → ℂ) : ℂ :=
  letI : MeasurableSpace G := borel G
  if h : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1
  then ∫ x in h.choose.2, Φ x ∂h.choose.1 else 0

theorem avg_const_mul (Γ : AddSubgroup G) (c : ℂ) (Φ : G → ℂ) : avg Γ (fun x => c * Φ x) = c * avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  simp only [avg]
  split_ifs
  · exact integral_const_mul _ _
  · simp

end Avg

section Adelic

variable (E : Type) [Field E] [NumberField E]

scoped instance instLC : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
scoped instance instSC : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
scoped instance t2Space_cuspAdeles : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E

def ratV (ι : Type) : AddSubgroup (ι → Ad E) :=
  (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι).range

theorem isCoLat_ratV (ι : Type) [Finite ι] : IsCoLat (ratV E ι) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
    obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have hW : IsOpen (Set.pi Set.univ fun _ : ι => V) :=
      isOpen_set_pi Set.finite_univ fun _ _ => hVo
    convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratV E ι)) using 1
    ext ⟨_, x, rfl⟩
    constructor
    · intro h p _
      have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
      exact h1.symm ▸ hV0
    · intro h
      have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
      subst hx
      exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
    refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    choose y hy using fun p => h (x p)
    refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
    change algebraMap E (Ad E) (-y p) + x p ∈ K
    rw [map_neg, neg_add_eq_sub]
    exact hy p

end Adelic

section Pos

variable {R : Type} [CommRing R] {a : ℕ} {ι : Type} [Fintype ι]

def IsNil (p : ι → Fin a × Fin a) : Prop := ∀ s t, (p s).2 ≠ (p t).1

def posM (p : ι → Fin a × Fin a) (x : ι → R) : Matrix (Fin a) (Fin a) R :=
  ∑ t, Matrix.single (p t).1 (p t).2 (x t)

theorem posM_mul {p : ι → Fin a × Fin a} (hp : IsNil p) (x y : ι → R) : posM p x * posM p y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (hp _ _) _

theorem posM_add (p : ι → Fin a × Fin a) (x y : ι → R) : posM p (x + y) = posM p x + posM p y := by
  simp only [posM, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

def posU {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) : GL (Fin a) R :=
  ⟨1 + posM p x, 1 - posM p x, by simp [mul_sub, add_mul, posM_mul hp], by simp [sub_mul, mul_add, posM_mul hp]⟩

theorem posU_val {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) : (posU hp x).val = 1 + posM p x := rfl

theorem posU_add {p : ι → Fin a × Fin a} (hp : IsNil p) (x y : ι → R) : posU hp (x + y) = posU hp x * posU hp y := by
  apply Units.ext
  change 1 + posM p (x + y) = (1 + posM p x) * (1 + posM p y)
  rw [posM_add]; simp only [mul_add, add_mul, one_mul, mul_one, posM_mul hp]; abel

theorem posU_zero {p : ι → Fin a × Fin a} (hp : IsNil p) : posU hp (0 : ι → R) = 1 := by
  apply Units.ext
  change 1 + posM p 0 = 1
  simp [posM]

theorem continuous_posU [TopologicalSpace R] [IsTopologicalRing R] {p : ι → Fin a × Fin a} (hp : IsNil p) :
    Continuous (posU hp : (ι → R) → GL (Fin a) R) := by
  have h : Continuous fun x : ι → R => posM p x := by
    refine continuous_finsetSum _ fun t _ => ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_apply t
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_const.add h, continuous_const.sub h⟩

abbrev UnipotentBlockColumnIndex (a r m : ℕ) : Type := {p : Fin a × Fin a // (p.1 : ℕ) < r ∧ r ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ m}

theorem isNil_blk (a r m : ℕ) : IsNil (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) := fun s t e => by
  have h1 := s.2.2.1
  have h2 := t.2.1
  rw [e] at h1
  omega

def blkU {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) : GL (Fin a) R := posU (isNil_blk a r m) x

end Pos

section Fn

variable {E : Type} [Field E] [NumberField E] {a : ℕ}


omit [NumberField E] in
theorem map_posU {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Fintype ι]
    {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) :
    GeneralLinearGroup.map φ (posU hp x) = posU hp (fun t => φ (x t)) := by
  apply Units.ext
  ext i j
  change φ ((1 + posM p x) i j) = (1 + posM p fun t => φ (x t)) i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add (f := _), map_sum, Matrix.one_apply, Matrix.single_apply]
  congr 1
  · split_ifs <;> simp
  · refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp

def dot {ι : Type} [Fintype ι] (ξ : ι → E) (x : ι → Ad E) : Ad E := ∑ t, algebraMap E (Ad E) (ξ t) * x t

def eLast (a k : ℕ) : UnipotentBlockColumnIndex a k k → E := fun t => if (t.1.1 : ℕ) + 1 = k then 1 else 0

structure StdPsi (ψ : AddChar (Ad E) ℂ) : Prop where
  cont : Continuous ψ
  norm : ∀ x, ‖ψ x‖ = 1
  rat : ∀ c : E, ψ (algebraMap E (Ad E) c) = 1
  ann : ∀ x, (∀ c : E, ψ (x * algebraMap E (Ad E) c) = 1) → ∃ d : E, x = algebraMap E (Ad E) d
  loc : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : w.adicCompletion E, ψ (sFin E (sLoc E w y)) ≠ 1

def coefF (ψ : AddChar (Ad E) ℂ) (k : ℕ) (ξ : UnipotentBlockColumnIndex a k k → E) (f : GA E a → ℂ) (g : GA E a) : ℂ :=
  avg (ratV E (UnipotentBlockColumnIndex a k k)) fun x => ψ (-dot ξ x) * f (blkU x * g)

def colT (ψ : AddChar (Ad E) ℂ) (k : ℕ) (f : GA E a → ℂ) : GA E a → ℂ := coefF ψ k (eLast a k) f

def whit (ψ : AddChar (Ad E) ℂ) (m : ℕ) : (GA E a → ℂ) → GA E a → ℂ :=
  Nat.rec (fun f => f) (fun m ih f => ih (colT ψ (m + 1) f)) m

theorem whit_succ (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : whit ψ (m + 1) f = whit ψ m (colT ψ (m + 1) f) := rfl

def IsMir (m : ℕ) (γ : GL (Fin a) E) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m < (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) E) i k

structure Good (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : Prop where
  cont : Continuous f
  left : ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, f (ratGL E a γ * g) = f g
  law : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g
  van : ∀ r, 0 < r → r ≤ m → ∀ g : GA E a, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun x => f (blkU x * g)) = 0

theorem ratGL_blkU {r m : ℕ} (c : UnipotentBlockColumnIndex a r m → E) :
    ratGL E a (blkU c) = blkU (fun t => algebraMap E (Ad E) (c t)) := map_posU _ _ _

theorem isMir_blkU {r m : ℕ} (c : UnipotentBlockColumnIndex a r m → E) : IsMir m (blkU c) := by
  intro i k h
  change (1 + posM Subtype.val c : Matrix (Fin a) (Fin a) E) i k = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, e2⟩
  rw [← e1, ← e2] at h
  omega

variable {ψ : AddChar (Ad E) ℂ}

theorem StdPsi.map_dot (hψ : StdPsi ψ) {ι : Type} [Fintype ι] (ξ c : ι → E) (x : ι → Ad E) :
    ψ (dot ξ ((fun t => algebraMap E (Ad E) (c t)) + x)) = ψ (dot ξ x) := by
  have : dot ξ ((fun t => algebraMap E (Ad E) (c t)) + x) =
      algebraMap E (Ad E) (∑ t, ξ t * c t) + dot ξ x := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
  rw [this, AddChar.map_add_eq_mul, hψ.rat, one_mul]

theorem continuous_dot {ι : Type} [Fintype ι] (ξ : ι → E) : Continuous (dot ξ : (ι → Ad E) → Ad E) :=
  continuous_finsetSum _ fun t _ => continuous_const.mul (continuous_apply t)

theorem per_blk {r m : ℕ} {f : GA E a → ℂ} (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex a r m → E) g, f (ratGL E a (blkU c) * g) = f g) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a r m)) (fun x => f (blkU x * g)) := by
  refine ⟨hc.comp ((continuous_posU _).mul continuous_const), ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a r m)) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  rw [e]
  change f (posU _ _ * g) = _
  rw [posU_add, mul_assoc]
  change f (blkU _ * _) = _
  rw [← ratGL_blkU, hl]
  rfl

theorem per_coef (hψ : StdPsi ψ) {k : ℕ} (ξ : UnipotentBlockColumnIndex a k k → E) {f : GA E a → ℂ} (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, f (ratGL E a (blkU c) * g) = f g) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a k k)) (fun x => ψ (-dot ξ x) * f (blkU x * g)) := by
  obtain ⟨h1, h2⟩ := per_blk hc hl g
  refine ⟨((hψ.cont.comp (continuous_dot ξ).neg).mul h1), ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e := h2 _ ⟨c, rfl⟩ x
  simp only at e ⊢
  rw [e, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
  congr 2
  exact hψ.map_dot ξ c x

end Fn

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineAtPlacesOverL : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := by
  first | exact @GlobalTheory.FontaineAdm.fontaineProperties_all_places | exact GlobalTheory.FontaineAdm.fontaineProperties_all_places | (intros; apply GlobalTheory.FontaineAdm.fontaineProperties_all_places <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AtQDTypes

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

theorem l_not_mem_gset {D : D7} (i : D.nd.Loc) (h : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) :
    D.nd.l i ∉ TwistedPlaces.gset D := by
  unfold TwistedPlaces.gset
  intro hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases h with h | h
  · exact (g_ne_q_d D 0).1 (hm ▸ h)
  · exact (g_ne_q_d D 0).2 (hm ▸ h)
  · exact (g_ne_q_d D 1).1 (hm ▸ h)
  · exact (g_ne_q_d D 1).2 (hm ▸ h)

end GlobalTheory.AtQDTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKRightExact

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

section Res

variable (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
  [IsScalarTower Qp L V] (ρ : Representation LL G V)

def res : Representation L G V where
  toFun g := (ρ g).restrictScalars L
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem Dcris_res : Dcris PD (res L ρ) = (Dcris PD ρ).restrictScalars L := by
  ext x
  simp only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem DdR_res : DdR PD (res L ρ) = (DdR PD ρ).restrictScalars L := by
  ext x
  simp only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem isCrys_res (h : IsCrys PD ρ) : IsCrys PD (res L ρ) := by
  unfold IsCrys at h ⊢
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h,
    mul_left_comm]

theorem isDR_of_res [FiniteDimensional L LL] (h : IsDR PD (res L ρ)) : IsDR PD ρ := by
  unfold IsDR at h ⊢
  rw [DdR_res] at h
  change finrank L ↥(DdR PD ρ) = _ at h
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V,
    mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

end Res

variable (f : V →ₗ[LL] V')

theorem map_φVB (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) x) =
      φVB PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_ιV (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) x) =
      ιV PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_mem_FilV {a : ℤ} {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_actVB {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g x) =
      actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

include PD in
theorem tmul_one_injective {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have h1 : (1 : B) ≠ 0 := fun h0 => PD.not_mem_filtration_two (by
    rw [← mul_one PD.t, h0, mul_zero, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp h1
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h
  simpa [hφ] using this

end Generic

theorem lift_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hs : Function.Surjective f) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ' ∧
      (∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) ∧
      ∀ y ∈ DdR (P.PD K) ρ', ∃ x ∈ DdR (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  have hc := isCrys_res (P.PD K) ↥L.1 ρ h
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1
  obtain ⟨-, h1⟩ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hc
  obtain ⟨h2, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hd
  rw [Dcris_res, Dcris_res] at h1
  rw [DdR_res, DdR_res] at h3
  refine ⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy, ha⟩
  exact ⟨x, hx.1, hxy⟩

theorem bkARightExact_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'
  haveI := hO.2.1
  obtain ⟨hdr, hl1, hl2⟩ := lift_periods T K LL A.ρ A'.ρ f hf hs hA
  obtain ⟨-, x', hx'⟩ := hc'
  obtain ⟨hd1, d₂', hd2, hfil⟩ := GlobalTheory.T.crystalline_coboundary_lift l P AI T K LL O hO A' hdr c' x' hx'
  obtain ⟨d₁, hd₁, e₁⟩ := hl1 _ hd1
  obtain ⟨d₂, hd₂, e₂⟩ := hl2 _ hd2
  obtain ⟨x, y, c, hy, hx1, hx2, hc, hcx⟩ := GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair l P AI T K LL O hO A d₁ hd₁ d₂ hd₂
  refine ⟨c, hc, ?_⟩
  rw [← hx1, map_sub, map_φVB] at e₁
  rw [← hx2, map_sub, map_ιV] at e₂
  obtain ⟨v, hv⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K LL A'.V).2
    (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x')
    (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁)
    (by
      have := Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil
      rw [← e₂] at this
      rw [map_sub]
      convert this using 1
      abel)
  refine ⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩
  have h1 := congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)
  rw [map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h1
  have h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    simp [actVB]
  change (A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
  rw [sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]
  abel

end GlobalTheory.BKRightExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExactStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bloch_kato_right_exact : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  first | exact @GlobalTheory.BKRightExact.bkARightExact_of_tied | exact GlobalTheory.BKRightExact.bkARightExact_of_tied | (intros; apply GlobalTheory.BKRightExact.bkARightExact_of_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def lfac {a b : ℕ} (σ : CG E a) (σ' : CG E b) (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  locL (Ideal.absNorm w.asIdeal) (sat σ w) ((sat σ' w).map (Units.map (starRingEnd ℂ).toMonoidHom)) s

def IsGood (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) ∧
    ∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w

def dcoef {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ :=
  ‖(((sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))).map (· ^ (r + 1))).sum‖ ^ 2 /
    ((r : ℝ) + 1)

def dexp (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ := ((r : ℝ) + 1) * Real.log (Ideal.absNorm w.asIdeal)

theorem dcoef_nonneg {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    0 ≤ dcoef σ σ' w r := div_nonneg (sq_nonneg _) (by positivity)

theorem dexp_nonneg (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : 0 ≤ dexp w r :=
  mul_nonneg (by positivity) (Real.log_nonneg (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast this.le))

end GlobalTheory.RSNonvan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.WhitCont

open GroundTheory.Automorphic.FourierWhittaker

theorem continuous_whit : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  intro E _ _ a F hF ⟨C, hC⟩
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hψ : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hj : Continuous fun p : GA E a × (Pos a → Ad E) =>
      F (uGL p.2 * p.1) * (GroundTheory.Global.adelicChar E (-supSum 0 p.2) : ℂ) :=
    (hF.comp ((continuous_uGL.comp continuous_snd).mul continuous_fst)).mul (hψ.comp continuous_snd)
  have e : GlobalTheory.JSW.whit F = fun g => ∫ X, F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂μ := rfl
  rw [e]
  set_option synthInstance.maxHeartbeats 200000 in
  refine continuous_of_dominated (bound := fun _ => C) (fun g => ?_) (fun g => ?_) (integrable_const C) ?_
  · have h1 : Continuous fun X : Pos a → Ad E => (g, X) := continuous_const.prodMk continuous_id
    exact (hj.comp h1).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hC _
  · refine Filter.Eventually.of_forall fun X => ?_
    exact (hF.comp (continuous_const.mul continuous_id)).mul continuous_const

end GlobalTheory.JSW.WhitCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem sst_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  intro l _ P AI T K V _ _ _ ρ hρ
  obtain ⟨ι, -, hι⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable l P AI T _ K V b ρ hρ
  refine GlobalTheory.T.isDeRham_of_invertible_periodMatrix l P _ K V b ρ (Matrix.GeneralLinearGroup.map ι.toRingHom Q) ?_
  intro g
  have hmap : ((Matrix.GeneralLinearGroup.map ι.toRingHom Q : GL (Fin (finrank ℚ_[l] V)) P.R.BdR) :
      Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) P.R.BdR)
      = (Q : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P)).map ι := rfl
  have h := congrArg (fun M => M.map ι) (hQ g)
  simp only [Matrix.map_mul, Matrix.map_map] at h
  rw [hmap]
  conv_rhs => rw [← h]
  congr 1
  · ext i j
    exact (ι.commutes _).symm
  · rw [Matrix.map_map]
    congr 1
    funext x
    exact (hι _ x).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistableStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_isSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.sst_isDR | exact GlobalTheory.sst_isDR | (intros; apply GlobalTheory.sst_isDR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnitPos

theorem prod_locUnit_eq_one_of_pos : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  intro F _ _ B _ ψ hker hd hconn a ha T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  have hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing F)ˣ :=
    GlobalTheory.RayFromArtin.mem_connectedComponentOfOne_of_pos a ha
  have hinf : ψ (ι u) = 1 := hconn _ ⟨u, hu, rfl⟩
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Ideles F := diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnitPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositiveStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  first | exact @GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | exact GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos | (intros; apply GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.RayRootOfUnity

theorem norm_pos_of_pos_real {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ τ : K →+* ℝ, 0 < τ x) : 0 < Algebra.norm ℚ x := by
  classical
  let c : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap ℚ K a)) = _
        rw [φ.commutes]; simp }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hφ : ∀ φ : K →ₐ[ℚ] ℂ, φ x ≠ 0 := fun φ => (map_ne_zero _).2 hx
  have hn : ∀ φ : K →ₐ[ℚ] ℂ, (‖φ x‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : K →ₐ[ℚ] ℂ, (φ x / (‖φ x‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ hne he => ?_)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · apply hne
      have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
        Complex.conj_eq_iff_re.1 (by rw [← hc, he])
      let τ : K →+* ℝ :=
        { toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
          map_add' := by simp, map_mul' := fun a b => by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_mul, hr, hr, hr, map_mul] }
      have hτ : 0 < (φ x).re := h τ
      rw [← hr x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      exact div_self (by exact_mod_cast hτ.ne')
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] at h1
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ x‖ := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h1]
    rfl
  have : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [h2]; exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
  exact_mod_cast this

theorem absNorm_modEq_one {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)} {p : ℕ}
    (hq : 𝔮 ≤ Ideal.span {(p : 𝓞 K)}) {I : Ideal (𝓞 K)} {α β : 𝓞 K} (hαβ : RayPair 𝔮 α β)
    (hI : I * Ideal.span {β} = Ideal.span {α}) : Ideal.absNorm I ≡ 1 [MOD p] := by
  obtain ⟨hα, hβ, _, hcβ, hd, hpos⟩ := hαβ
  have hpos' : 0 < Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have hx : ((α * β : 𝓞 K) : K) ≠ 0 := by simpa using mul_ne_zero hα hβ
    have := norm_pos_of_pos_real hx fun τ => by
      have := hpos τ
      simpa [map_mul] using this
    rw [← Algebra.coe_norm_int, map_mul] at this
    exact_mod_cast this
  have h1 := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at h1
  have h2 : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β * Algebra.norm ℤ β = Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have e := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs] at e
    have e2 : (Ideal.absNorm I : ℤ) * |Algebra.norm ℤ β| * |Algebra.norm ℤ β| =
        |Algebra.norm ℤ α| * |Algebra.norm ℤ β| := by rw [e]
    rw [mul_assoc, abs_mul_abs_self, ← abs_mul, abs_of_pos hpos'] at e2
    rw [mul_assoc]; exact e2
  have h3 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (hq hd)
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcβ
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h4 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (x := b * β) (y := 1) (by
    have : b * β - 1 = -v := by linear_combination huv
    rw [this]; exact neg_mem (hq hv))
  rw [map_mul, map_one] at h4
  have h5 := congrArg (Int.cast : ℤ → ZMod p) h2
  push_cast at h4 h5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * h5 +
    ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * ((Algebra.norm ℤ β : ℤ) : ZMod p) * h3 +
    (((Algebra.norm ℤ b : ℤ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) + 1) * (1 - (Ideal.absNorm I : ZMod p)) * h4

end GlobalTheory.RayRootOfUnity

namespace GlobalTheory.RayRootOfUnity

theorem exists_isPrimitiveRoot_of_isRay : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∃ ζ : H, IsPrimitiveRoot ζ n := by
  intro K H _ _ _ _ _ _ n hn hR
  classical
  have hRF : GlobalTheory.Mem.Fld.IsRayField K H (Ideal.span {(n : 𝓞 K)}) := ⟨inferInstance, hR⟩
  have h𝔮 : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by simpa using hn
  let ψ : H →+* ℂ := (IsAlgClosed.lift : H →ₐ[ℚ] ℂ).toRingHom
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨S, hSa, hS⟩ := GlobalTheory.Mem.BaseField.exists_gens H
  obtain ⟨L, hfd, hgal, hSL, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert z S) (by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    exacts [GlobalTheory.Mem.BaseField.isAlgebraic_exp n, hSa w hw])
  have hψL : ∀ x, ψ x ∈ L := hS L (fun w hw => hSL w (Finset.mem_insert_of_mem hw)) ψ
  have hzL : z ∈ L := hSL z (Finset.mem_insert_self _ _)
  have : NumberField L := {}
  letI : Algebra H L := (ψ.codRestrict L hψL).toAlgebra
  letI : Algebra K L := ((ψ.codRestrict L hψL).comp (algebraMap K H)).toAlgebra
  have : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  obtain ⟨x, hx⟩ := GlobalTheory.Mem.RayZeta.root_mem_rayField K H L _ n hn le_rfl hRF
    (GlobalTheory.RayMaximal.closure_isFrob_eq_top L h𝔮)
    (fun I α β hαβ hI => absNorm_modEq_one le_rfl hαβ hI) ⟨z, hzL⟩
    (Subtype.ext (by simpa using hz.pow_eq_one))
  have e : ψ x = z := congrArg Subtype.val hx
  exact ⟨x, IsPrimitiveRoot.of_map_of_injective (f := ψ) (by rw [e]; exact hz) ψ.injective⟩

end GlobalTheory.RayRootOfUnity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulusStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveRoot_in_rayClassField_natModulus : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∃ ζ : H, IsPrimitiveRoot ζ n := by
  first | exact @GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | exact GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | (intros; apply GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem Dst_spans_tensor_Bst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∀ v : V, ∃ (k : ℕ) (a : Fin k → Bst P) (x : Fin k → V ⊗[ℚ_[l]] Bst P), (∀ i, x i ∈ Dst P ρ) ∧ v ⊗ₜ[ℚ_[l]] (1 : Bst P) = ∑ i, onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] (a i)) (x i) := by
  intro l _ P AI T K V _ _ _ ρ hS v
  set b := Module.finBasis ℚ_[l] V with hb
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable l P AI T (Fin (finrank ℚ_[l] V)) K V b ρ hS
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] (Bst P) V (Fin (finrank ℚ_[l] V)) b

  have hst : ∀ g : ↥(GK K), (stRep P ρ g : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap := by
    intro g; apply TensorProduct.ext'; intro w c; rfl
  have hon : ∀ f : End ℚ_[l] (Bst P), (onB P ℚ_[l] V f : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map LinearMap.id f := by
    intro f; apply TensorProduct.ext'; intro w c; rfl
  set w : Fin (finrank ℚ_[l] V) → Bst P := fun i => algebraMap ℚ_[l] (Bst P) (b.repr v i) with hw
  let Qm : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := Q.1
  let Qi : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := (Q⁻¹).1
  refine ⟨finrank ℚ_[l] V, Matrix.mulVec Qi w, fun j => e.symm (fun i => Qm i j), ?_, ?_⟩
  · intro j
    rw [mem_Dst]
    intro g
    apply e.injective
    rw [hst g, he3, LinearEquiv.apply_symm_apply]
    have h : ∀ i, (((LinearMap.toMatrix b b) (ρ g)).map ⇑(algebraMap ℚ_[l] (Bst P)) * (Q.1).map ⇑((actSt P) ↑g)) i j = Qm i j :=
      fun i => congrFun (congrFun (hQ g) i) j
    funext i
    rw [← h i]
    rfl
  · apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext i
    rw [he1, Finset.sum_apply]
    have key : ∀ j, e (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] ((Matrix.mulVec Qi w) j)) (e.symm (fun i => Qm i j))) i =
        (Matrix.mulVec Qi w) j * Qm i j := by
      intro j
      rw [hon, he3, LinearEquiv.apply_symm_apply, LinearMap.toMatrix_id, Matrix.map_one (algebraMap ℚ_[l] (Bst P)) (map_zero _) (map_one _), Matrix.one_mulVec]
      rfl
    simp_rw [key]
    have hQQ : Qm * Qi = 1 := by
      show (Q * Q⁻¹).1 = 1
      rw [mul_inv_cancel]; rfl
    have := congrFun (congrArg (fun M => Matrix.mulVec M w) hQQ) i
    simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at this
    rw [Algebra.smul_def, mul_one]
    refine this.symm.trans ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.Pst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRingStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∀ v : V, ∃ (k : ℕ) (a : Fin k → Bst P) (x : Fin k → V ⊗[ℚ_[l]] Bst P), (∀ i, x i ∈ Dst P ρ) ∧ v ⊗ₜ[ℚ_[l]] (1 : Bst P) = ∑ i, onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] (a i)) (x i) := by
  first | exact @GlobalTheory.Pst.Dst_spans_tensor_Bst | exact GlobalTheory.Pst.Dst_spans_tensor_Bst | (intros; apply GlobalTheory.Pst.Dst_spans_tensor_Bst <;> assumption)
end
end

module

public import Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfKapUnit

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03 Module

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem jb_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

theorem jb_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := jb_Fil_anti PD hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ h]
  have e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem jb_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (jb_FilV_anti PD (min_le_left a b) ha)
      (jb_FilV_anti PD (min_le_right a b) hb)⟩

theorem jb_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hc : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨t, rfl⟩ := hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (PD.Fil a).smul_of_tower_mem _ f.2
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact add_mem hx hy
  have h0 : e y = 0 := by
    ext i
    exact PD.Fil_sep _ (fun a => hc a y (hy a) i)
  exact e.injective (by rw [h0, map_zero])

theorem jb_FildR_anti (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) :=
  fun _ _ hab => inf_le_inf_left _ (jb_FilV_anti PD hab)

theorem jb_bound (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ a₀ a₁ : ℤ, ∀ a, IsJumpV PD ρ τ a → a₀ ≤ a ∧ a ≤ a₁ := by
  classical
  set D := DdRE PD ρ τ with hD
  have hFD : ∀ a, FildR PD ρ τ a ≤ D := fun a => inf_le_left

  let bD := Module.finBasis LL ↥D
  have hex : ∀ j, ∃ a, ((bD j : ↥D) : V ⊗[Qp] BdR) ∈ FilV PD (LL := LL) (V := V) a :=
    fun j => jb_FilV_exh PD (LL := LL) (V := V) _
  choose aj haj using hex
  set a₀ : ℤ := -(∑ j, |aj j|) with ha₀
  have ha₀j : ∀ j, a₀ ≤ aj j := by
    intro j
    have h1 : |aj j| ≤ ∑ k, |aj k| :=
      Finset.single_le_sum (f := fun k => |aj k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := neg_abs_le (aj j)
    linarith
  have hlow : ∀ a, a ≤ a₀ → FildR PD ρ τ a = D := by
    intro a ha
    refine le_antisymm (hFD a) (le_inf le_rfl ?_)
    have hspan : (Submodule.span LL (Set.range bD)).map D.subtype = D := by
      rw [bD.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact jb_FilV_anti PD (ha.trans (ha₀j j)) (haj j)

  let f : ℕ → ℕ := fun k => finrank LL ↥(FildR PD ρ τ (k : ℤ))
  have hne : ∃ m, ∃ k, f k = m := ⟨_, 0, rfl⟩
  let m := Nat.find hne
  obtain ⟨k₀, hk₀⟩ := Nat.find_spec hne
  have hmin : ∀ k, m ≤ f k := fun k => Nat.find_min' hne ⟨k, rfl⟩
  have hfinF : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    fun a => Submodule.finiteDimensional_of_le (hFD a)
  have hstab : ∀ k : ℕ, k₀ ≤ k → FildR PD ρ τ (k : ℤ) = FildR PD ρ τ (k₀ : ℤ) := by
    intro k hk
    have hle : FildR PD ρ τ (k : ℤ) ≤ FildR PD ρ τ (k₀ : ℤ) := jb_FildR_anti PD ρ τ (by exact_mod_cast hk)
    have hr1 : f k ≤ f k₀ := Submodule.finrank_mono hle
    have hr2 := hmin k
    exact Submodule.eq_of_le_of_finrank_eq hle (by show f k = f k₀; omega)
  have hbot : FildR PD ρ τ (k₀ : ℤ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply jb_FilV_sep PD (LL := LL) (V := V) x
    intro a
    rcases le_total a (k₀ : ℤ) with h | h
    · exact jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg k₀) h)
      have hk : k₀ ≤ k := by exact_mod_cast h
      rw [← hstab k hk] at hx
      exact hx.2
  have hhigh : ∀ a, (k₀ : ℤ) ≤ a → FildR PD ρ τ a = ⊥ := fun a ha =>
    eq_bot_iff.mpr (hbot ▸ jb_FildR_anti PD ρ τ ha)
  refine ⟨a₀, (k₀ : ℤ) - 1, fun a ha => ⟨?_, ?_⟩⟩
  · by_contra hlt
    exact ha (by rw [hlow a (by omega), hlow (a + 1) (by omega)])
  · by_contra hlt
    exact ha (by rw [hhigh a (by omega), hhigh (a + 1) (by omega)])

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem jumpsBdd_holds (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL) (hK : Function.Bijective (algebraMap K₀ K)) :
    ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.LiftingTheory.JumpsLet W T M h := by
  intro T hT
  have hfin : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ) :=
    fun τ => ((hDR hK T.V T.ρ T.cont hT.2.2.2).2 τ).1
  choose a₀ a₁ hab using fun τ => jb_bound PD T.ρ τ (hfin τ)
  refine ⟨fun _ => Finset.univ.sup (fun τ => (-a₀ τ).toNat),
    fun _ => Finset.univ.sup (fun τ => (a₁ τ).toNat), ?_⟩
  intro i τ _ a ha
  obtain ⟨h0, h1⟩ := hab τ a ha
  have e0 : (-a₀ τ).toNat ≤ Finset.univ.sup (fun τ => (-a₀ τ).toNat) :=
    Finset.le_sup (f := fun τ => (-a₀ τ).toNat) (Finset.mem_univ τ)
  have e1 : (a₁ τ).toNat ≤ Finset.univ.sup (fun τ => (a₁ τ).toNat) :=
    Finset.le_sup (f := fun τ => (a₁ τ).toNat) (Finset.mem_univ τ)
  have f0 := Int.self_le_toNat (-a₀ τ)
  have f1 := Int.self_le_toNat (a₁ τ)
  have g0 : (((-a₀ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (-a₀ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e0
  have g1 : (((a₁ τ).toNat : ℕ) : ℤ) ≤ ((Finset.univ.sup (fun τ => (a₁ τ).toNat) : ℕ) : ℤ) := by exact_mod_cast e1
  simp only [Set.mem_Icc]
  constructor <;> omega

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.LevBMemFil
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem levB_mem_fil (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (ζ : Rs LL PD.p s) (x : ↥(W.N T)) (k : ℤ) :
    (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c) ∈ FilD W T c s (-k) := by
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 ζ.2
  show ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ x k) ∈ FilLev W T c s (-k)
  rw [← hLb]
  exact (hP4 T hcrys c s ζ hprim).1 x k


open Classical in
theorem expN_mem_xi (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (x : ↥(W.N T)) :
    expN Lb s T c x ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) := by
  rw [xi_iff]
  intro ζ k
  have e1 : cf (expN Lb s T c x) k = coefN Lb s T c x k := rfl
  rw [e1, coefN, evaluation_expansion_at_root]
  exact levB_mem_fil hP4 hcrys hLb s ζ x k

end Formalism.MainNotions.N.Ln03.K8

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GaloisActionFrobeniusComm
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {hR : Ring9 W}

section Letters

variable {T : LocLat G Qp LL O}

theorem galois_action_frobenius_comm (g : G) (z : T.V ⊗[Qp] B) :
    actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) z) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem scalar_mul_frobenius_comm (k : K₀) (z : T.V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ k) (φVB PD (LL := LL) (V := T.V) z) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [mulVB, φVB, map_mul, PD.φ_K₀]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem frobenius_maps_letter_succ (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) z ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz1 hz2 ⊢
  refine ⟨fun g => ?_, fun k => ?_⟩
  · rw [galois_action_frobenius_comm, hz1 g]
  · obtain ⟨k', rfl⟩ := PD.σ_bij.2 k
    have he : W.emb (i + 1) (PD.σ k') = W.emb i k' := by
      have := congrArg (fun f : K₀ →ₐ[Qp] LL => f k') (W.emb_σ i)
      simpa only [AlgHom.comp_apply] using this
    rw [scalar_mul_frobenius_comm, hz2 k', map_smul, he]

theorem frobenius_pow_maps_letter (m : ℕ) (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ m) z ∈
      DcrisL PD T.ρ (W.emb (i + (m : ZMod n))) := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact frobenius_maps_letter_succ _ _ ih

theorem lambda_mem_dcris_letter (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (x : C.V)
    (hx : C.t (c - (ell : ZMod n)) x ∈ W.N T) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hx⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
  have h1 : (⟨_, hx⟩ : ↥(W.N T)) = (letE (c - (ell : ZMod n)) : LetA O n) • ⟨_, hx⟩ :=
    Subtype.ext (C.t_letter _ x).symm
  have h2 := frobenius_pow_maps_letter ell _ _ (W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hx⟩)
  rw [sub_add_cancel] at h2
  rw [h1]
  exact h2

theorem lambda_coe_eq_frobenius_pow (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) {r : ℕ} (e : Fin r → C.V)
    (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hk⟩) := by
  unfold lamOf
  rw [dite_eq_left hk, dite_eq_left (lambda_mem_dcris_letter C c ell (e k) hk)]

end Letters

section Coords

variable {T : LocLat G Qp LL O}

theorem coord_t_sum (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type} (s : Finset ι) (g : ι → C.V) :
    C.t i (∑ l ∈ s, g l) = ∑ l ∈ s, C.t i (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Coord.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coord.t_add, ih]

theorem coord_t_const_smul (C : Coord W (baseIdOf hR) T) (i : ZMod n) (a : O) (x : C.V) :
    C.t i (PowerSeries.C a • x) = a • C.t i x := by
  rw [C.t_smul, show PowerSeries.C a = algebraMap O (PowerSeries O) a from rfl, AlgHom.commutes,
    algebraMap_smul]

theorem exists_pi0_eq_letPi_mul (hR : Ring9 W) : ∃ u : LetA O n, W.π₀ = (letπ : LetA O n) * u := by
  obtain ⟨w, -, hw⟩ := π₀₁_eq hR
  have hp : 1 ≤ PD.p - 1 := by
    have := PD.hp.two_le
    omega
  refine ⟨fun _ => w * PowerSeries.X ^ (PD.p - 1 - 1), ?_⟩
  funext j
  show W.π₀₁ = PowerSeries.X * (w * PowerSeries.X ^ (PD.p - 1 - 1))
  rw [hw]
  conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
  ring

theorem comparison_pi0_smul_eq_zero (hR : Ring9 W) (y : ↥(W.N T)) : W.cmp T (W.π₀ • y) = 0 := by
  obtain ⟨u, hu⟩ := exists_pi0_eq_letPi_mul hR
  rw [hu, mul_smul]
  exact W.cmp_π T (u • y)

end Coords

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {r₁ r₂ : ℕ}

theorem lambda_of_matrixCongruences (hC : CoordHom C₁ C₂ F) (hD : MemD W F c) (e₁ : Fin r₁ → C₁.V)
    (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (prLIs : ∀ k, (latHomOf hC).f (e₁ k) -
        ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
      E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n)))) :
    ∀ k, dmapOf hD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  intro k
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (prLIs k)
  have hX := hyx
  rw [LinearMap.lsmul_apply] at hX
  change (PowerSeries.X : PowerSeries O) • y = hC.f (e₁ k) - ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l at hX
  have hfe : hC.f (e₁ k) =
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l + (PowerSeries.X : PowerSeries O) • y := by
    rw [hX]
    abel
  have ht : C₂.t (c - (ell : ZMod n)) (hC.f (e₁ k)) =
      ∑ l, (LinearMap.toMatrix' P l k) • C₂.t (c - (ell : ZMod n)) (e₂ l) +
        W.π₀ • C₂.t (c - (ell : ZMod n)) y := by
    rw [hfe, Coord.t_add, coord_t_sum, C₂.t_smul, BaseId.d_X]
    simp only [coord_t_const_smul]
  have hy' : C₂.t (c - (ell : ZMod n)) y ∈ W.N T₂ := hy
  have hx : W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) ∈ W.N T₂ :=
    W.map_N F hC.crys hC.crys' _ (he₁ k)
  have hsplit : (⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ : ↥(W.N T₂)) =
      ∑ l, (LinearMap.toMatrix' P l k) •
          (⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ : ↥(W.N T₂)) +
        W.π₀ • (⟨C₂.t (c - (ell : ZMod n)) y, hy'⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    show W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) = _
    rw [← hC.coord_hom_map_trace, ht]
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  have hcmp : W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
        W.cmp T₂ ⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_add (f := _), map_sum, comparison_pi0_smul_eq_zero hR, add_zero]
    simp only [W.cmp_smul]
  have hL : ∀ l, ((lamOf C₂ c ell e₂ l : Dc W T₂ c) : T₂.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
        (W.cmp T₂ ⟨_, he₂ l⟩) := fun l => lambda_coe_eq_frobenius_pow C₂ c ell e₂ l (he₂ l)
  apply Subtype.ext
  calc ((dmapOf hD (lamOf C₁ c ell e₁ k) : Dc W T₂ c) : T₂.V ⊗[Qp] B)
      = pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₁ ⟨_, he₁ k⟩)) := by
        rw [← lambda_coe_eq_frobenius_pow C₁ c ell e₁ k (he₁ k)]
        rfl
    _ = ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩) := by
        rw [← pfMapFl_φpow F ell, ← W.cmp_map F hC.crys hC.crys' ⟨_, he₁ k⟩ hx]
    _ = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
          ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
            (W.cmp T₂ ⟨_, he₂ l⟩) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hcmp, map_sum]
        simp only [map_smul]
    _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, hL]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.FrameBound
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.USideFree
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FinalAllB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.BaseChangeNB
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PJEigB
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdIrrEquivOfOrdered
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.SplitRead GlobalTheory.ProdReorder

noncomputable section

namespace GlobalTheory.CompanionTheory.SegReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem famCongr {u : ℕ} {f g : Fin u → IrrGL (k := k)} (hfg : ∀ i, f i = g i) {T : ℕ}
    (e : (Σ i, Fin (f i).1) ≃ Fin T) (e' : (Σ i, Fin (g i).1) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (f i).rep).Equiv (multiProd e' fun i => (g i).rep)) := by
  obtain rfl : f = g := funext hfg
  exact multiProd_placing e e' _

end GlobalTheory.CompanionTheory.SegReorder
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.JB

section Gen

variable {Γ V W : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eqv_apply {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (g : Γ) (v : V) :
    φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v

theorem fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) (v : V) :
    v ∈ GlobalTheory.PRep.fixed ρ K → φ.toLinearEquiv v ∈ GlobalTheory.PRep.fixed σ K := by
  intro hv
  rw [mem_fixed_iff'] at hv ⊢
  intro k hk
  rw [← eqv_apply, hv k hk]

theorem map_fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) :
    (GlobalTheory.PRep.fixed ρ K).map (φ.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.fixed σ K := by
  ext x
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have := fixed_eqv φ K _ h
    rwa [LinearEquiv.apply_symm_apply] at this
  · intro h
    have := fixed_eqv φ.symm K _ h
    exact this

theorem finrank_fixed_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) :
    Module.finrank ℂ (GlobalTheory.PRep.fixed ρ K) = Module.finrank ℂ (GlobalTheory.PRep.fixed σ K) :=
  (LinearEquiv.ofSubmodules φ.toLinearEquiv _ _ (map_fixed_eqv φ K)).finrank_eq

theorem hkG_eqv {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (φ : ρ.Equiv σ) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite) (v : V) :
    φ.toLinearEquiv (hkG ρ K f v) = hkG σ K f (φ.toLinearEquiv v) := by
  unfold hkG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum_eq ρ K f hfin.coe_toFinset.ge, hsum_eq σ K f hfin.coe_toFinset.ge, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, eqv_apply]

end Gen

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def JE (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLw a w × GLw b w) V) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

theorem je_eqv (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GLw a w × GLw b w) V}
    {σ : Representation ℂ (GLw a w × GLw b w) W} (φ : ρ.Equiv σ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) :
    JE w ϖ ρ ξa ξb → JE w ϖ σ ξa ξb := by
  rintro ⟨v, hv, hne, hev⟩
  refine ⟨φ.toLinearEquiv v, fixed_eqv φ _ v hv, fun h0 => hne (φ.toLinearEquiv.map_eq_zero_iff.1 h0),
    fun x y hx hy => ?_⟩
  rw [← hkG_eqv φ _ _ (pair_double_coset_finite_support w ϖ x y), hev x y hx hy, map_smul]

theorem dl_add {N : ℕ} (w : Pl E) (x x' : Fin N → ℤ) : dl w (x + x') = dl w x * dl w x' := by
  unfold dl
  rw [← zpow_add₀ (qh_ne w)]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pw_add {N : ℕ} (ξ : Fin N → ℂˣ) (x x' : Fin N → ℤ) : pw ξ (x + x') = pw ξ x * pw ξ x' := by
  unfold pw
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem pair_eigenvalue_add (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x x' : Fin a → ℤ) (y y' : Fin b → ℤ) :
    ev2 w ξa ξb (x + x') (y + y') = ev2 w ξa ξb x y * ev2 w ξa ξb x' y' := by
  unfold ev2
  rw [dl_add, dl_add, pw_add, pw_add]
  ring

theorem dl_ne {N : ℕ} (w : Pl E) (x : Fin N → ℤ) : dl w x ≠ 0 := zpow_ne_zero _ (qh_ne w)

theorem pw_ne {N : ℕ} (ξ : Fin N → ℂˣ) (x : Fin N → ℤ) : pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem pair_eigenvalue_ne_zero (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    ev2 w ξa ξb x y ≠ 0 :=
  mul_ne_zero (mul_ne_zero (dl_ne w x) (pw_ne ξa x)) (mul_ne_zero (dl_ne w y) (pw_ne ξb y))

theorem dl_zero {N : ℕ} (w : Pl E) : dl w (0 : Fin N → ℤ) = 1 := by
  unfold dl
  simp

theorem pw_zero {N : ℕ} (ξ : Fin N → ℂˣ) : pw ξ 0 = 1 := by
  unfold pw
  simp

theorem pw_single {N : ℕ} (ξ : Fin N → ℂˣ) (i : Fin N) : pw ξ (Pi.single i 1) = ξ i := by
  unfold pw
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

def x0 (N : ℕ) : Fin N → ℤ := fun i => -(2 * ((i : ℕ) : ℤ))

theorem gap_base (N : ℕ) : Gap (x0 N) := by
  intro i j hij
  have : (i : ℕ) < j := hij
  simp only [x0]
  omega

theorem gap_base_add_single {N : ℕ} (i : Fin N) : Gap (x0 N + Pi.single i 1) := by
  intro i' j' h
  have h' : (i' : ℕ) < j' := h
  simp only [Pi.add_apply, x0, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> subst_vars <;> omega

def probe (w : Pl E) (p : (Fin a → ℂˣ) × (Fin b → ℂˣ)) : Option (Fin a ⊕ Fin b) → ℂ
  | none => ev2 w p.1 p.2 (x0 a) (x0 b)
  | some (Sum.inl i) => ev2 w p.1 p.2 (x0 a + Pi.single i 1) (x0 b)
  | some (Sum.inr j) => ev2 w p.1 p.2 (x0 a) (x0 b + Pi.single j 1)

theorem probe_inj (w : Pl E) : Function.Injective (probe (a := a) (b := b) w) := by
  intro p p' h
  have h0 := congrFun h none
  simp only [probe] at h0
  have ha : ∀ i, ev2 w p.1 p.2 (Pi.single i 1) 0 = ev2 w p'.1 p'.2 (Pi.single i 1) 0 := by
    intro i
    have hi := congrFun h (some (Sum.inl i))
    simp only [probe] at hi
    have e1 := pair_eigenvalue_add w p.1 p.2 (x0 a) (Pi.single i 1) (x0 b) 0
    have e2 := pair_eigenvalue_add w p'.1 p'.2 (x0 a) (Pi.single i 1) (x0 b) 0
    rw [add_zero] at e1 e2
    rw [e1, e2, h0] at hi
    exact mul_left_cancel₀ (pair_eigenvalue_ne_zero w _ _ _ _) hi
  have hb : ∀ j, ev2 w p.1 p.2 0 (Pi.single j 1) = ev2 w p'.1 p'.2 0 (Pi.single j 1) := by
    intro j
    have hj := congrFun h (some (Sum.inr j))
    simp only [probe] at hj
    have e1 := pair_eigenvalue_add w p.1 p.2 (x0 a) 0 (x0 b) (Pi.single j 1)
    have e2 := pair_eigenvalue_add w p'.1 p'.2 (x0 a) 0 (x0 b) (Pi.single j 1)
    rw [add_zero] at e1 e2
    rw [e1, e2, h0] at hj
    exact mul_left_cancel₀ (pair_eigenvalue_ne_zero w _ _ _ _) hj
  refine Prod.ext (funext fun i => Units.ext ?_) (funext fun j => Units.ext ?_)
  · have := ha i
    simp only [ev2, dl_zero, pw_zero, pw_single, mul_one] at this
    exact mul_left_cancel₀ (dl_ne w _) this
  · have := hb j
    simp only [ev2, dl_zero, pw_zero, pw_single, one_mul] at this
    exact mul_left_cancel₀ (dl_ne w _) this

theorem je_finite (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLw a w × GLw b w) V) [FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w))] :
    {p : (Fin a → ℂˣ) × (Fin b → ℂˣ) | JE w ϖ ρ p.1 p.2}.Finite := by
  let pt : Option (Fin a ⊕ Fin b) → (Fin a → ℤ) × (Fin b → ℤ)
    | none => (x0 a, x0 b)
    | some (Sum.inl i) => (x0 a + Pi.single i 1, x0 b)
    | some (Sum.inr j) => (x0 a, x0 b + Pi.single j 1)
  have hpt : ∀ (o : Option (Fin a ⊕ Fin b)) (p : (Fin a → ℂˣ) × (Fin b → ℂˣ)),
      probe w p o = ev2 w p.1 p.2 (pt o).1 (pt o).2 := by
    intro o p
    rcases o with _ | i | j <;> rfl
  have hgap : ∀ o, Gap (pt o).1 ∧ Gap (pt o).2 := by
    intro o
    rcases o with _ | i | j
    · exact ⟨gap_base a, gap_base b⟩
    · exact ⟨gap_base_add_single i, gap_base b⟩
    · exact ⟨gap_base a, gap_base_add_single j⟩
  let T : Option (Fin a ⊕ Fin b) → Module.End ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w)) := fun o =>
    hkW ρ (I2 a b w) (dc2 w ϖ (pt o).1 (pt o).2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)
  refine Set.Finite.of_finite_image (f := probe w) ?_ (probe_inj w).injOn
  refine (Set.Finite.pi (t := fun o => {μ | (T o).HasEigenvalue μ})
    fun o => Module.End.finite_hasEigenvalue (T o)).subset ?_
  rintro _ ⟨p, ⟨v, hv, hne, hev⟩, rfl⟩ o _
  show (T o).HasEigenvalue (probe w p o)
  rw [hpt o p]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hv⟩) ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_smul]
    show ((hkW ρ (I2 a b w) _ _ _ ⟨v, hv⟩ : GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) = _
    rw [hkW_apply]
    exact hev _ _ (hgap o).1 (hgap o).2
  · intro h0
    exact hne (congrArg Subtype.val h0)

end Place

section Cls

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fd_pair (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)) := by
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  exact GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ (lp Pa w) (lp Pb w) (iwGL a w) (iwGL b w)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pa.h (fun i => Pa.σ i w)).2 _ (hIa 1).2.1 (hIa 1).2.2.1)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pb.h (fun i => Pb.σ i w)).2 _ (hIb 1).2.1 (hIb 1).2.2.1)

def key {n : ℕ} (P₀ : Pre E n) (w : Pl E) (P : Pre E n) : Fin P₀.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) :=
  if h : P₀.c = P.c then fun j => P.cls (Fin.cast h j) w else fun j => P₀.cls j w

theorem c_eq {n : ℕ} {P₀ P : Pre E n} (hP : PreEquiv P₀ P) : P₀.c = P.c := by
  obtain ⟨e, -, -⟩ := hP
  simpa using Fintype.card_congr e

theorem lp_equiv_cast {n : ℕ} (P : Pre E n) (w : Pl E) {c₀ : ℕ} (h : c₀ = P.c) :
    ∃ e : (Σ j : Fin c₀, Fin (P.cls (Fin.cast h j) w).1) ≃ Fin n,
      Nonempty ((lp P w).Equiv (GlobalTheory.SmGL.multiProd e fun j => (P.cls (Fin.cast h j) w).rep)) := by
  subst h
  exact ⟨GlobalTheory.SmGL.stdBlocks P.N P.h, ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i =>
    GlobalTheory.LocGL.IrrGL.equivOf (P.σ i w).ρ (P.σ i w).smooth (P.σ i w).irred⟩⟩

theorem key_mem {n : ℕ} (P₀ P : Pre E n) (w : Pl E) (hP : PreEquiv P₀ P) :
    key P₀ w P ∈ Set.univ.pi (fun _ => Set.range fun i => P₀.cls i w) := by
  have hc := c_eq hP
  obtain ⟨e, he, -⟩ := hP
  intro j _
  simp only [key, dif_pos hc]
  exact ⟨e.symm (Fin.cast hc j), by show P₀.cls _ w = _; rw [he, Equiv.apply_symm_apply]⟩

theorem key_eqv {n : ℕ} (P₀ P Q : Pre E n) (w : Pl E) (hP : P₀.c = P.c) (hQ : P₀.c = Q.c)
    (hk : key P₀ w P = key P₀ w Q) : Nonempty ((lp P w).Equiv (lp Q w)) := by
  simp only [key, dif_pos hP, dif_pos hQ] at hk
  obtain ⟨e1, ⟨φ1⟩⟩ := lp_equiv_cast P w hP
  obtain ⟨e2, ⟨φ2⟩⟩ := lp_equiv_cast Q w hQ
  obtain ⟨ψ⟩ := GlobalTheory.CompanionTheory.SegReorder.famCongr (f := fun j => P.cls (Fin.cast hP j) w)
    (g := fun j => Q.cls (Fin.cast hQ j) w) (fun j => congrFun hk j) e1 e2
  exact ⟨(φ1.trans ψ).trans φ2.symm⟩

def Good (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)))
    (p : Pre E a × Pre E b) : Prop :=
  PreEquiv Pa p.1 ∧ PreEquiv Pb p.2 ∧ key Pa w p.1 = κ.1 ∧ key Pb w p.2 = κ.2

def ZS (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E))) :
    Set ((Fin a → ℂˣ) × (Fin b → ℂˣ)) :=
  if h : ∃ p, Good Pa Pb w κ p then {ξ | JEig h.choose.1 h.choose.2 w ϖ ξ.1 ξ.2} else ∅

def fr (w : Pl E) (p : Pre E a × Pre E b) : ℕ := Module.finrank ℂ (GlobalTheory.PRep.fixed (pairAt p.1 p.2 w) (I2 a b w))

def MS (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E))) : ℕ :=
  if h : ∃ p, Good Pa Pb w κ p then fr w h.choose else 0

theorem zs_finite (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E))) :
    (ZS Pa Pb w ϖ κ).Finite := by
  unfold ZS
  split_ifs with h
  · have := fd_pair h.choose.1 h.choose.2 w
    exact je_finite w ϖ (pairAt h.choose.1 h.choose.2 w)
  · exact Set.finite_empty

theorem pair_eqv (Pa Qa : Pre E a) (Pb Qb : Pre E b) (w : Pl E) (φa : (lp Pa w).Equiv (lp Qa w))
    (φb : (lp Pb w).Equiv (lp Qb w)) : Nonempty ((pairAt Pa Pb w).Equiv (pairAt Qa Qb w)) :=
  ⟨GlobalTheory.SmGL.RowOneCell.extTensorEquiv φa φb⟩

theorem step (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (Pa' Qa : Pre E a) (Pb' Qb : Pre E b)
    (ha : PreEquiv Pa Pa') (hb : PreEquiv Pb Pb') (hqa : PreEquiv Pa Qa) (hqb : PreEquiv Pb Qb)
    (hka : key Pa w Qa = key Pa w Pa') (hkb : key Pb w Qb = key Pb w Pb') :
    fr w (Pa', Pb') = fr w (Qa, Qb) ∧
      ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → JEig Qa Qb w ϖ ξa ξb := by
  have ea : Nonempty ((lp Pa' w).Equiv (lp Qa w)) := key_eqv Pa Pa' Qa w (c_eq ha) (c_eq hqa) hka.symm
  have eb : Nonempty ((lp Pb' w).Equiv (lp Qb w)) := key_eqv Pb Pb' Qb w (c_eq hb) (c_eq hqb) hkb.symm
  have e : Nonempty ((pairAt Pa' Pb' w).Equiv (pairAt Qa Qb w)) := pair_eqv Pa' Qa Pb' Qb w ea.some eb.some
  exact ⟨finrank_fixed_eqv e.some _, fun ξa ξb hJ => je_eqv w ϖ e.some ξa ξb hJ⟩

theorem mem_zs (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)))
    (h : ∃ p, Good Pa Pb w κ p) (ξ : (Fin a → ℂˣ) × (Fin b → ℂˣ)) (hJ : JEig h.choose.1 h.choose.2 w ϖ ξ.1 ξ.2) :
    ξ ∈ ZS Pa Pb w ϖ κ := by
  unfold ZS
  rw [dif_pos h]
  exact hJ

theorem ms_eq (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
    (κ : (Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)))
    (h : ∃ p, Good Pa Pb w κ p) : MS Pa Pb w κ = fr w h.choose :=
  dif_pos h

theorem jEigFin_at (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa' : Pre E a) (Pb' : Pre E b),
      PreEquiv Pa Pa' → PreEquiv Pb Pb' →
      Module.finrank ℂ (GlobalTheory.PRep.fixed (pairAt Pa' Pb' w) (I2 a b w)) ≤ m ∧
        ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  let KS : Set ((Fin Pa.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) × (Fin Pb.c → GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E))) :=
    (Set.univ.pi fun _ => Set.range fun i => Pa.cls i w) ×ˢ (Set.univ.pi fun _ => Set.range fun i => Pb.cls i w)
  have hKS : KS.Finite :=
    (Set.Finite.pi fun _ => Set.finite_range _).prod (Set.Finite.pi fun _ => Set.finite_range _)
  refine ⟨⋃ κ ∈ KS, ZS Pa Pb w ϖ κ, ∑ κ ∈ hKS.toFinset, MS Pa Pb w κ,
    hKS.biUnion fun κ _ => zs_finite Pa Pb w ϖ κ, fun Pa' Pb' ha hb => ?_⟩
  have hκS : (key Pa w Pa', key Pb w Pb') ∈ KS := ⟨key_mem Pa Pa' w ha, key_mem Pb Pb' w hb⟩
  have h : ∃ p, Good Pa Pb w (key Pa w Pa', key Pb w Pb') p := ⟨(Pa', Pb'), ha, hb, rfl, rfl⟩
  have hG : Good Pa Pb w (key Pa w Pa', key Pb w Pb') h.choose := h.choose_spec
  have hs := step Pa Pb w ϖ Pa' h.choose.1 Pb' h.choose.2 ha hb hG.1 hG.2.1 hG.2.2.1 hG.2.2.2
  exact ⟨show fr w (Pa', Pb') ≤ _ from (hs.1.trans (ms_eq Pa Pb w _ h).symm).trans_le
      (Finset.single_le_sum (f := MS Pa Pb w) (fun _ _ => Nat.zero_le _) (hKS.mem_toFinset.2 hκS)),
    fun ξa ξb hJ => Set.mem_biUnion hκS (mem_zs Pa Pb w ϖ _ h (ξa, ξb) (hs.2 ξa ξb hJ))⟩

end Cls

theorem jEigFin : JEigFin := fun _ _ _ _ _ _ Pa Pb w ϖ _ => jEigFin_at Pa Pb w ϖ

end PositivityTheory.Rg.BcB.F.Tail.JB
end
end

namespace UpperTheory.BaseChangeIdentities

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F in
theorem baseChangeNB : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  Plug2B.bci_of
    (HeckeLevelFrameExistence.frameEx_of_fin uSide (FX.candFin_of_jEigFin Tail.JB.jEigFin))
    FrameWordIdentity.frameBound FinalAllB.frameRead_holdsB

end UpperTheory.BaseChangeIdentities
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.Strong
noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.GalOfCusp PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange UpperTheory.V.Z.Tf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Desc

def WeakAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

theorem weakAll_of (hR : SR.SplitRigid) (hN : GlobalTraceComparison.PartNorm) (hU : GOne.UnitOf) (hRun : GlobalTraceComparison.RunTh) : WeakAll := by
  intro E _ _ _ hE n hn π hreg hd hsat
  rcases hRun E hE n hn π hreg hd hsat with h | ⟨D, h1, h2, -, h4⟩
  · exact h
  refine absurd (hR E hE n hn (CG.mk π) (hU E n hn π hd) (Fin D.c) D.N D.P D.pos (fun i => ?_) (h4.mono fun w hw hs => ?_)) h1
  · obtain ⟨P, e, -, hu⟩ := hN E n hn π hd D h2 h4 i
    rw [← e]
    exact (CG.isUnitary_mk P).2 hu
  · obtain ⟨B, ⟨b, hb, rfl⟩, hB⟩ := hw hs
    exact ⟨b, hb, hB⟩

theorem len_one {q d : ℕ} (hq : 1 < q) (hd : 1 ≤ d) (z : ℂ)
    (h : ∀ k : Fin d, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖z * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))‖ ∧
      ‖z * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))‖ < (q : ℝ) ^ (1 / 2 : ℝ)) : d = 1 := by
  by_contra hne
  have hq0 : 0 < q := by omega
  have hq1 : (0 : ℝ) < q := by exact_mod_cast hq0
  have h0 := (h ⟨0, by omega⟩).2
  have h1 := (h ⟨1, by omega⟩).1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq0] at h0 h1
  have e0 : (((d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)).re = ((d : ℝ) - 1) / 2 := by simp
  have e1 : (((d : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)).re = ((d : ℝ) - 1) / 2 - 1 := by simp
  simp only at h0 h1
  rw [e0] at h0
  rw [e1, Real.rpow_sub hq1, Real.rpow_one, ← mul_div_assoc, lt_div_iff₀ hq1] at h1
  have e2 : (q : ℝ) ^ (-(1 / 2) : ℝ) * q = (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hq1.ne']
    norm_num
  linarith

theorem match_of (hB : BcSpeh) (h1 : CompUnique) (h3 : OneFactor) (hJ : GlobalTheory.Published.JacquetShalikaBound)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) (hR : SR.SplitRigid) (hT : GOne.Thin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : GlobalTheory.BCT.Unr E) {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hu : (CG.mk π).IsUnitary) (U : Submodule ℂ (UA E n → ℂ)) (hU : IsAutRepU U)
    (hun : ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU U w)
    (hae : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w →
      ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) :
    GlobalTheory.Cong.Match U π := by
  obtain ⟨c, a, d, h, P, ρ, m, σ, hP, hsp, hsplit⟩ := hB E hE n hn U hU
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w → ∃ (B : Multiset ℂˣ) (S : Fin c → Multiset ℂˣ),
      (CG.mk π).HasSat w B ∧ (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
      ∑ i, ∑ k : Fin (d i), (S i).map (fun z : ℂˣ => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
        B.map (fun z : ℂˣ => (z : ℂ)) := hae.mono fun w hw hs => by
    obtain ⟨τ, B, t1, t2, t3⟩ := hw hs
    obtain ⟨e⟩ := h1 E n U hU w hs τ
      { V := _, ρ := locProd h w (σ · w), smooth := isSmooth_parInd _ _, irred := (hsplit w hs).1 } t1 (hsplit w hs)
    obtain ⟨S, s1, s2⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hP.pos i).2)
      (fun i => (hsp i w).2.2) B (GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv e.toLinearEquiv
        (fun g x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x) t2)
    exact ⟨B, S, t3, fun i => (GlobalTheory.BcSpehCompare.hasSat_iff (hP.loc i w) _).2 (s1 i), by
      simpa only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] using s2⟩
  have hd : ∀ i, d i = 1 := fun i => by
    obtain ⟨w, hs, hw⟩ := (hT E).2.exists_notMem_finite (eventually_cofinite.1 key)
    obtain ⟨B, S, b1, b2, b3⟩ := not_not.1 hw hs
    obtain ⟨z, hz⟩ : ∃ z, z ∈ S i := Multiset.card_pos_iff_exists_mem.mp (by rw [(b2 i).card]; exact (hP.pos i).1)
    have hq : 1 < Ideal.absNorm w.asIdeal := by
      have a0 : Ideal.absNorm w.asIdeal ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      have a1 : Ideal.absNorm w.asIdeal ≠ 1 := fun e => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
      omega
    refine len_one hq (hP.pos i).2 (z : ℂ) fun k => ?_
    have hm : (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ)) ∈ B.map (fun z : ℂˣ => (z : ℂ)) := by
      rw [← b3]
      exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Multiset.mem_sum.2 ⟨k, Finset.mem_univ _, Multiset.mem_map_of_mem _ hz⟩⟩
    obtain ⟨α, hα, e⟩ := Multiset.mem_map.1 hm
    rw [← e]
    exact hJ E n _ hu w B b1 α hα
  obtain rfl : d = fun _ => 1 := funext hd
  obtain ⟨j, hj⟩ := hR E hE n hn (CG.mk π) hu (Fin c) a (fun i => CG.mk (P i)) (fun i => (hP.pos i).1)
    (fun i => GlobalTheory.CuspRep.CsdUnitary.isUnitary_of_isCsd E _ (CG.mk (P i)) (hP.csd i)) (key.mono fun w hw hs => by
      obtain ⟨B, S, b1, b2, b3⟩ := hw hs
      refine ⟨S, b2, ?_⟩
      have e : ∑ i, S i = B := by
        apply Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective
        rw [← b3]
        exact (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ)) S Finset.univ).trans (by simp)
      rwa [e])
  have haj : a j = n := congrArg Sigma.fst hj
  have hone : ∀ i, i = j := fun i => by
    by_contra hij
    have h2 : 1 * a i + 1 * a j ≤ ∑ k, 1 * a k := by
      rw [← Finset.sum_pair (f := fun k => 1 * a k) hij]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := (hP.pos i).1
    have h' : ∑ k, 1 * a k = n := h
    omega
  obtain rfl : c = 1 := by
    have := Fintype.card_eq_one_iff.2 ⟨j, hone⟩
    simpa using this
  obtain rfl : j = 0 := Subsingleton.elim _ _
  obtain rfl : a = fun _ => n := funext fun i => by rw [hone i, haj]
  have hπ : P 0 = π := CuspSub.ext (hM E n _ _ (eq_of_heq (Sigma.mk.inj hj).2))
  subst hπ
  refine ⟨hU, hun, fun w hw σ' hσ' => ?_, fun τ' lam hl => ?_⟩
  · obtain ⟨e₁⟩ := h3 E w n h (ρ 0 w) (σ · w) (hsp 0 w).2.2
    obtain ⟨e₂⟩ := LocUniq.isLocComp_unique (P 0) w _ _ (hP.loc 0 w) hσ'
    exact GlobalTheory.BaseChangeBridge.isCompAlong_of_equiv (e₁.trans e₂).toLinearEquiv
      (fun g x => LinearMap.congr_fun ((e₁.trans e₂).toIntertwiningMap.isIntertwining' g) x) σ'.irred (hsplit w hw)
  · have hw := hP.weight τ' lam hl
    rw [Fin.sum_univ_one] at hw
    rw [← hw, show spehInf 1 (m 0 τ') = m 0 τ' by simp [spehInf]]
    exact CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hP.inf 0 τ')

theorem desc_of (hB : BcSpeh) (h1 : CompUnique) (h3 : OneFactor) (hJ : GlobalTheory.Published.JacquetShalikaBound)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) (hR : SR.SplitRigid) (hT : GOne.Thin) (hU : GOne.UnitOf) (hW : WeakAll) :
    GlobalTheory.Cong.Desc := by
  intro E _ _ _ l a _ ha π ⟨hreg, hpol, hg, _⟩
  have hE : GlobalTheory.BCT.Unr E := fun w => by
    by_cases hs : IsSplitAt w
    · exact GlobalTheory.SplitUnram.isUnramifiedAt_of_isSplitAt E w hs
    · exact (hg.2.2 w hs).2.1
  have hd : GlobalTheory.ContraPair.DualIsConj π := by
    have := hpol.dual
    rwa [map_pow, compNorm_quadChar, one_pow, GlobalTheory.ContraPair.dualIsConjBy_one] at this
  obtain ⟨U, u1, u2, u3⟩ := hW E hE a ha π hreg hd fun w hw => (hg.2.2 w hw).2.2
  exact ⟨U, match_of hB h1 h3 hJ hM hR hT hE ha π (hU E a ha π hd) U u1 u2 u3⟩

end UpperTheory.Gal.Desc
end
end

open UpperTheory.V.Z.Tf PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.Gal.Desc

theorem speh : GlobalTheory.BcSpeh.BcSpeh := UpperTheory.BaseChangeIdentities.speh UpperTheory.BaseChangeIdentities.baseChangeNB

theorem weakAll : WeakAll := weakAll_of SR.splitRigid (GaloisFromTraceFormula.partNorm GaloisFromTraceFormula.absInf) GOne.unitOf GaloisFromTraceFormula.runTh

theorem desc : GlobalTheory.Cong.Desc :=
  desc_of speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin GOne.unitOf weakAll

theorem descOffT : GlobalTheory.Cong.DescOffT := GlobalTheory.Cong.descOffT_of_desc desc

end UpperTheory.Gal.Desc

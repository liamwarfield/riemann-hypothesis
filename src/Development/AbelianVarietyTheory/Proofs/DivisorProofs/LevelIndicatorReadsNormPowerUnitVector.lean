module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjConjNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTopOfOneMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

variable {D : D7}

theorem star_eq (x : D.host.E) : star x = D.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

theorem smul_finRat (S T : HSp D) (s : D.host.E) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    incA D s • GlobalTheory.VacUnique.finRat S T γ = GlobalTheory.VacUnique.finRat S T (s • γ) := by
  ext i j
  change incA D s * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ i j) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (s * γ i j)
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

section Lat

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem mem_latRat_iff (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS) (hLT : IsStdLat LT)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    γ ∈ GlobalTheory.LatVac.latRat S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) ↔
      ∀ i j, γ i j ∈ D.host.AA0 := by
  rw [← GlobalTheory.AdForm.RatLat.AA_eq hcc]
  have hg : ∀ (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) i j,
      GlobalTheory.LatVac.genMap S T a s t i j = a * t i * star (s j) := fun a s t i j => by
    simp [GlobalTheory.LatVac.genMap, gS, Matrix.one_apply]
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      obtain ⟨b, hb⟩ := (hLS s).1 hs j
      obtain ⟨b', hb'⟩ := (hLT t).1 ht i
      have e : a * t i * star (s j) = (b' * D.host.conj • b : 𝓞 D.host.E) • a := by
        rw [← hb, ← hb', star_eq]
        change a * (b' : D.host.E) * D.host.conj (b : D.host.E) = ((b' : D.host.E) * D.host.conj (b : D.host.E)) * a
        ring
      rw [hg, e]
      exact (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha
    | zero => exact fun i j => D.host.AA.zero_mem
    | add x y _ _ hx hy => exact fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hx i j) (hy i j)
    | neg x _ hx => exact fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hx i j)
  · intro h
    rw [Matrix.matrix_eq_sum_single γ]
    refine sum_mem fun i _ => sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨γ i j, h i j, Pi.single j 1, (hLS _).2 fun k => ?_, Pi.single i 1, (hLT _).2 fun k => ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, rfl⟩, ⟨0, rfl⟩]
    · rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, rfl⟩, ⟨0, rfl⟩]
    · refine Matrix.ext fun k l => ?_
      rw [hg, Matrix.single_apply, Pi.single_apply, Pi.single_apply]
      by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, eq_comm (a := k), eq_comm (a := l)]

theorem finRat_mem_iff (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T γ ∈ latO S T LS LT (fun _ => True) ↔ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank) := by
  rw [GlobalTheory.OddGenus.mem_iff_entries, ← mem_latRat_iff hcc gS hLS hLT]
  exact GlobalTheory.AdForm.RatLat.finTens_mem_iff hψ hS hT γ

theorem half_mem_iff (hcc : D.host.ccK = ⊤) (hLS : IsStdLat LS) (hLT : IsStdLat LT) (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) (t : WO S T)
    (ht : IsHalf (cA D e) t) :
    t ∈ latO S T LS LT (fun _ => True) ↔ ∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have fr : ∀ {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}, IsStdLat L →
      Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (EAf D)) L := fun {n L} h => by
    have e : L = Formalism.UG.stdLat (n := Fin n) (A := D.host.E) (𝓞 D.host.E) := by
      ext y
      rw [h, Formalism.UG.stdLat, Submodule.mem_pi]
      exact ⟨fun H i _ => H i, fun H i => H i trivial⟩
    exact e ▸ Formalism.L2.DIV.frame_standard D.host.F D.host.E n
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T LS LT 1 1 hS hT (fr hLS) (fr hLT) _ _
    (GlobalTheory.RefDatumLev.isIdemSum_conjPl he.1) ?_ t ht]
  · simp only [IsIntM, frMapO, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_apply]
  · intro Q hQ h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hQ
    rw [hcc, Ideal.absNorm_top, mul_one] at h
    have h' : Formalism.L2.DIV.starOHom ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := h
    rw [map_natCast] at h'
    refine he.2 w hw ?_
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h'

theorem approx (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {k : ℕ} (hk : 0 < k) {u : WO S T}
    (hu : u ∈ latO S T LS LT (fun _ => True)) :
    ∃ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank), ∃ v ∈ latO S T LS LT (fun _ => True),
      u = GlobalTheory.VacUnique.finRat S T γ + k • v := by
  have hi := GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  obtain ⟨ρ, ⟨M, rfl⟩, v, hv, h⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).2.1
    (incA D (k : D.host.E)⁻¹ • u) (Matrix.ext fun i j => by
      have : infPart D (u i j) = 0 := congrFun (congrFun hi i) j
      change infPart D (incA D (k : D.host.E)⁻¹ * u i j) = 0
      rw [RingHom.map_mul, this, mul_zero])
  have hv' := GlobalTheory.VacUnique.latO_inf S T _ _ _ hv
  have e1 : incA D (k : D.host.E)⁻¹ • u = GlobalTheory.VacUnique.finRat S T M + v := by
    refine GlobalTheory.AdForm.RatLat.eq_of_parts (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
    · have h1 : infPart D (u i j) = 0 := congrFun (congrFun hi i) j
      have h2 : infPart D (v i j) = 0 := congrFun (congrFun hv' i) j
      have h3 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      change infPart D (incA D (k : D.host.E)⁻¹ * u i j) = infPart D (GlobalTheory.VacUnique.finRat S T M i j + v i j)
      rw [RingHom.map_mul, RingHom.map_add (f := _), h1, h2, h3, mul_zero, add_zero]
    · have h1 : finPart D (incA D (k : D.host.E)⁻¹ * u i j - incA D (M i j) - v i j) = 0 := congrFun (congrFun h i) j
      have h3 : finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := rfl
      change finPart D (incA D (k : D.host.E)⁻¹ * u i j) = finPart D (GlobalTheory.VacUnique.finRat S T M i j + v i j)
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at h1
      rw [RingHom.map_add (f := _), h3, h1]
  have e2 : u = GlobalTheory.VacUnique.finRat S T (k • M) + k • v := by
    rw [map_nsmul, ← smul_add, ← e1, smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hk]
  refine ⟨k • M, (finRat_mem_iff hψ hcc gS hLS hLT hS hT _).1 ?_, v, hv, e2⟩
  rw [← sub_eq_iff_eq_add] at e2
  rw [← e2]
  exact sub_mem hu (nsmul_mem hv k)

end Lat

theorem smul_mem_skew (I : Ideal (𝓞 D.host.E)) {a d : ℕ} {s : D.host.E}
    (hs : s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))))
    {γ : Matrix (Fin d) (Fin a) D.host.E} (hγ : γ ∈ YYl D (stdL D a) (stdL D d)) :
    s • γ ∈ YYl D (stdL D a) (skewLat D I d) := by
  induction hγ using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    refine Submodule.subset_span ⟨c, hc, s • A, ?_, smul_comm _ _ _⟩
    clear hc
    induction hA using Submodule.span_induction with
    | mem A hA =>
      refine Submodule.subset_span fun x hx i _ => ?_
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hA x hx i trivial)
      rw [Matrix.smul_mulVec, Pi.smul_apply, ← hb, smul_eq_mul, mul_comm]
      exact Submodule.smul_mem _ b hs
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem skew_mem_closure (I : Ideal (𝓞 D.host.E)) {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ YYl D (stdL D a) (skewLat D I d)) :
    z ∈ AddSubgroup.closure {w : Matrix (Fin d) (Fin a) D.host.E |
      ∃ s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D a) (stdL D d), w = s • γ} := by
  have hA : ∀ A ∈ homL D (stdL D a) (skewLat D I d), ∀ i j,
      A i j ∈ (((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      intro i j
      have := hA (Pi.single j 1) (fun k _ => by
        rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨1, rfl⟩, zero_mem _]) i trivial
      rwa [Matrix.mulVec_single_one] at this
    | zero => exact fun i j => zero_mem _
    | add x y _ _ hx hy => exact fun i j => add_mem (hx i j) (hy i j)
    | smul c x _ hx => exact fun i j => Submodule.smul_mem _ c (hx i j)
  suffices h : ∀ r : 𝓞 D.host.E, r • z ∈ AddSubgroup.closure {w : Matrix (Fin d) (Fin a) D.host.E |
      ∃ s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D a) (stdL D d), w = s • γ} by simpa using h 1
  induction hz using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA', rfl⟩ := hB
    intro r
    rw [Matrix.matrix_eq_sum_single (r • c • A)]
    refine sum_mem fun i _ => sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨A i j, hA A hA' i j, Matrix.single i j (r • c), (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_, ?_⟩
    · rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hc
      · exact D.host.AA0.zero_mem
    · rw [Matrix.smul_single, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_comm]
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [smul_add]; exact add_mem (hx r) (hy r)
  | smul c x _ hx => intro r; rw [smul_smul]; exact hx _

theorem mul_mem_of_skew {I : Ideal (𝓞 D.host.E)} (hI : D.host.conj • I ≠ ⊥) {s : D.host.E}
    (hs : s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))))
    {m : 𝓞 D.host.E} (hm : m ∈ D.host.conj • I) : ∃ b ∈ I, (b : D.host.E) = m * s := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hI)] at hs
  obtain ⟨b, hb, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hs _ (FractionalIdeal.mem_coeIdeal_of_mem _ hm))
  exact ⟨b, hb, e.trans (mul_comm _ _)⟩

theorem smul_skew_mem {I : Ideal (𝓞 D.host.E)} (hI : D.host.conj • I ≠ ⊥) {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ YYl D (stdL D a) (skewLat D I d)) {m : 𝓞 D.host.E} (hm : m ∈ D.host.conj • I) :
    (m : D.host.E) • z ∈ YYl D (stdL D a) (stdL D d) := by
  have h := skew_mem_closure I hz
  clear hz
  induction h using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hw
    obtain ⟨b, -, e⟩ := mul_mem_of_skew hI hs hm
    rw [smul_smul, ← e]
    exact Submodule.smul_mem _ b hγ
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem conj_mul_conj : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun x => by
    change D.host.conj (D.host.conj x) = x
    rw [← star_eq, ← star_eq, star_star]

theorem conj_conj_smul (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  rw [smul_smul, conj_mul_conj, one_smul]

theorem mem_conj_smul {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} : b ∈ D.host.conj • I ↔ D.host.conj • b ∈ I := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_eq_of_mul_eq_one_right conj_mul_conj]

theorem cA_incA_int (b : 𝓞 D.host.E) :
    cA D (incA D (b : D.host.E)) = incA D ((D.host.conj • b : 𝓞 D.host.E) : D.host.E) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_eq]
  rfl

theorem modul_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : modul P c ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_add_two {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P)
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : ∃ m ∈ modul P c, ∃ u : 𝓞 D.host.E, m + u * 2 = 1 := by
  have h : IsCoprime (modul P c) (Ideal.span {2}) := IsCoprime.prod_left fun w hw => IsCoprime.pow_left (by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine w.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => he.2 w hw ?_)
    have h2 : (2 : 𝓞 D.host.E) ∈ w.asIdeal := h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    obtain ⟨k, hk⟩ := D.host.two_dvd_QS
    rw [hk, mul_assoc, mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h2)
  obtain ⟨m, hm, t, ht, e⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  exact ⟨m, hm, u, e⟩

theorem eq_top_of_one_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {I : Ideal (𝓞 E)}
    (hI : I ≠ ⊥) (h : (1 : Formalism.L2.Herm.intAf F E) ∈ Formalism.L2.DIV.idS F I) : I = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  apply Formalism.L2.DIV.cmpS_inj (F := F) I hI
  rw [map_one, map_one, map_zero, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact h

theorem isCoprime_conj {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : IsCoprime (D.host.conj • modul P c) (modul P c) := by
  obtain ⟨-, h1, t, ht, h2⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e P c he
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (1 - cA D e)) := by
    rw [CosetCong.inId_iff, map_sub, map_one]
    exact (CosetCong.conj_idem c he).2
  obtain ⟨h4, h5⟩ := h3
  have h6 : (1 : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      Formalism.L2.DIV.idS D.host.F (D.host.conj • modul P c ⊔ modul P c) := by
    have e1 : (1 : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, h1⟩ * ⟨_, h4⟩ + t := by
      apply Subtype.ext
      change (1 : EAf D) = toEAf D e * toEAf D (1 - cA D e) + (t : EAf D)
      rw [h2, ← RingHom.map_mul, mul_sub, he.2, mul_one, sub_zero, add_sub_cancel]
    rw [e1]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.map_mono le_sup_left h5)) (Ideal.map_mono le_sup_right ht)
  exact Ideal.isCoprime_iff_sup_eq.2
    (eq_top_of_one_mem (fun h => modul_ne_bot P c (le_bot_iff.1 (le_sup_right.trans h.le))) h6)

theorem toEAf_surj : Function.Surjective (toEAf D) := fun z => by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul a α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] a, rfl⟩
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, RingHom.map_add _ _ _⟩

theorem half_ext {S T : HSp D} {a : Formalism.L2.Theta.AE D} (ha : infPart D a = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf a y)
    (h : ∀ i j, toEAf D (x i j) = toEAf D (y i j)) : x = y := by
  refine GlobalTheory.AdForm.RatLat.eq_of_parts (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
  · change infPart D (x i j) = infPart D (y i j)
    rw [← hx, ← hy, RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul]
  · exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h i j)

theorem inId_mul {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {x : Formalism.L2.Theta.AE D}
    (hx : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (incA D (b : D.host.E) * x)) := by
  have h1 : Formalism.L2.DIV.oToS D.host.F D.host.E b * ⟨_, hx⟩ ∈ Formalism.L2.DIV.idS D.host.F I :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
  rw [RingHom.map_mul]
  exact ⟨mul_mem (Formalism.L2.DIV.oToS D.host.F D.host.E b).2 hx, h1⟩

theorem inId_add {I : Ideal (𝓞 D.host.E)} {x y : EAf D} (hx : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I y) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  exact ⟨add_mem h1 h3, add_mem h2 h4⟩

end GlobalTheory.SkewLevel

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • modul P c ≠ ⊥ := fun h => modul_ne_bot P c (by rw [← conj_conj_smul (modul P c), h, Ideal.smul_bot])

theorem conj_conj_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) :
    D.host.conj • D.host.conj • modul P c ≠ ⊥ := by
  rw [conj_conj_smul]
  exact modul_ne_bot P c

theorem kill (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {I : Ideal (𝓞 D.host.E)} {y u : WO S T}
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) (hu : u ∈ latO S T LS LT (fun _ => True))
    {b : 𝓞 D.host.E} (hb : b ∈ D.host.conj • I) : ψ (symplO S T (incA D (b : D.host.E) • u) y) = 1 := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_int]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu (hy _ (mem_conj_smul.1 hb))

theorem smul_finRat_mem (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P : Finset (Formalism.L2.DIV.Pl D.host.E))
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    ∀ m ∈ modul P c, incA D (m : D.host.E) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) := fun m hm => by
  rw [smul_finRat, finRat_mem_iff hψ hcc gS hLS hLT hS hT]
  exact smul_skew_mem (conj_conj_ne_bot P c) hz (by rwa [conj_conj_smul])

theorem kill_of_inId (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) {I : Ideal (𝓞 D.host.E)} {t y : WO S T}
    (ht : IsHalf (cA D e) t) (hI : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • I) (toEAf D (t i j)))
    (hy : ∀ m ∈ I, incA D (m : D.host.E) • y ∈ latO S T LS LT (fun _ => True)) : ψ (symplO S T t y) = 1 := by
  obtain ⟨hinf, hint, -⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props _ _ (fun _ => 0) (GlobalTheory.RefDatumLev.isIdemSum_conjPl he.1)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he.1]
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (D.host.conj • I))
  have hfI : ∀ k, f k ∈ D.host.conj • I := fun k => hf ▸ Submodule.subset_span ⟨k, rfl⟩
  have hc : ∀ i j, ∃ c : Fin n → Formalism.L2.Theta.AE D, (∀ k, toEAf D (c k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      toEAf D (t i j) = ∑ k, toEAf D (incA D (f k : D.host.E)) * toEAf D (c k) := fun i j => by
    obtain ⟨h1, h2⟩ := hI i j
    have e1 : Formalism.L2.DIV.idS D.host.F (D.host.conj • I) =
        Ideal.span (Set.range fun k => Formalism.L2.DIV.oToS D.host.F D.host.E (f k)) := by
      rw [Formalism.L2.DIV.idS, ← hf]
      refine (Ideal.map_span _ _).trans ?_
      rw [← Set.range_comp]
      rfl
    rw [e1, Ideal.mem_span_range_iff_exists_fun] at h2
    obtain ⟨r, hr⟩ := h2
    choose c hc using fun k => toEAf_surj (D := D) (r k : EAf D)
    refine ⟨c, fun k => hc k ▸ (r k).2, ?_⟩
    have h3 := congrArg (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype hr
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h3
    refine h3.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, hc, mul_comm]
    rfl
  choose c hc1 hc2 using hc
  let u : Fin n → WO S T := fun k => Matrix.of fun i j => cA D e * c i j k
  have hu1 : ∀ k, IsHalf (cA D e) (u k) := fun k i j => by
    change cA D e * (cA D e * c i j k) = cA D e * c i j k
    rw [← mul_assoc, hee]
  have hu2 : ∀ k, u k ∈ latO S T LS LT (fun _ => True) := fun k =>
    (half_mem_iff hcc hLS hLT hS hT he _ (hu1 k)).2 fun i j => by
      change toEAf D (cA D e * c i j k) ∈ _
      rw [RingHom.map_mul]
      exact mul_mem hint (hc1 i j k)
  have hent : ∀ i j, (∑ k, incA D (f k : D.host.E) • u k) i j = cA D e * ∑ k, incA D (f k : D.host.E) * c i j k :=
    fun i j => by
      rw [Matrix.sum_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have e2 : t = ∑ k, incA D (f k : D.host.E) • u k := half_ext hinf ht
    (fun i j => by rw [hent, ← mul_assoc, hee]) fun i j => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hent, ← ht i j, RingHom.map_mul, RingHom.map_mul, hc2, map_sum]
      simp only [RingHom.map_mul]
  rw [e2]
  exact Finset.sum_induction _ (fun t => ψ (symplO S T t y) = 1)
    (fun a b ha hb => by rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, ha, hb, one_mul])
    (by rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]) fun k _ => kill hψ hS hT hy (hu2 k) (hfI k)

theorem inId_of_kill (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {t : WO S T}
    (ht : IsHalf (cA D e) t) (htΛ : t ∈ latO S T LS LT (fun _ => True))
    (hk : ∀ z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank),
      ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T z)) = 1) (i j) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (t i j)) := by
  have hN : 0 < Ideal.absNorm (D.host.conj • D.host.conj • modul P c) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (conj_conj_ne_bot P c))
  have h1 : ∀ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
      toEAf D (incA D (star s) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun s hs => by
    have hh : IsHalf (cA D e) (incA D (star s) • t) := fun i j => by
      change cA D e * (incA D (star s) * t i j) = incA D (star s) * t i j
      rw [mul_left_comm, ht]
    refine (half_mem_iff hcc hLS hLT hS hT he _ hh).1 ?_ i j
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1 _ (Matrix.ext fun i j => ?_)).2 fun u hu => ?_
    · have : infPart D (t i j) = 0 := congrFun (congrFun (GlobalTheory.VacUnique.latO_inf S T _ _ _ htΛ) i) j
      change infPart D (incA D (star s) * t i j) = 0
      rw [RingHom.map_mul, this, mul_zero]
    · obtain ⟨γ, hγ, v, hv, rfl⟩ := approx hψ hcc gS hLS hLT hS hT hN hu
      obtain ⟨b, -, hb⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (Ideal.absNorm_mem _)
      have e1 : incA D s • Ideal.absNorm (D.host.conj • D.host.conj • modul P c) • v = incA D (b : D.host.E) • v := by
        rw [hb, mul_comm, RingHom.map_mul, mul_smul]
        congr 1
        rw [← Nat.cast_smul_eq_nsmul (Formalism.L2.Theta.AE D)]
        congr 1
        exact (map_natCast ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm
      rw [GlobalTheory.PlaceModel.symplO_smul, GlobalTheory.DualPairCheck.cA_incA, star_star, smul_add, GlobalTheory.PlaceModel.symplO_add_right,
        AddChar.map_add_eq_mul, smul_finRat, hk _ (smul_mem_skew _ hs hγ), one_mul, e1]
      exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT htΛ (GlobalTheory.VacSign.smul_mem_latO b hv)
  have h2 : ∀ r ∈ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (incA D (star r) * t i j)) := fun r hr => by
    rw [← div_mul_cancel₀ ((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
      (FractionalIdeal.coeIdeal_ne_zero.2 (conj_conj_ne_bot P c))] at hr
    refine FractionalIdeal.mul_induction_on hr (fun s hs m hm => ?_) fun x y hx hy => ?_
    · obtain ⟨m, hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
      have e1 : star (s * algebraMap (𝓞 D.host.E) D.host.E m) = ((D.host.conj • m : 𝓞 D.host.E) : D.host.E) * star s := by
        rw [star_mul, star_eq (algebraMap (𝓞 D.host.E) D.host.E m)]
        rfl
      rw [e1, RingHom.map_mul (incA D), mul_assoc]
      exact inId_mul (mem_conj_smul.1 hm') (h1 s hs)
    · rw [star_add, RingHom.map_add (f := _), add_mul, RingHom.map_add (f := _)]
      exact inId_add hx hy
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he.1 c)
  have h3 := h2 _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))
  have e2 : star (algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • a)) = (a : D.host.E) := by
    change star (D.host.conj (a : D.host.E)) = _
    rw [← star_eq, star_star]
  have e3 : t i j = incA D (b : D.host.E) * t i j + incA D (a : D.host.E) * t i j := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← add_mul, ← RingHom.map_add (f := _), this, RingHom.map_one, one_mul]
  rw [e2] at h3
  rw [e3, RingHom.map_add (f := _)]
  exact inId_add (inId_mul hb ((half_mem_iff hcc hLS hLT hS hT he _ ht).1 htΛ i j)) h3

theorem heisO_eq_half (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) {vac : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ YYl D (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :
    heisO ψ S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) vac = heisO ψ S T (GlobalTheory.VacUnique.finRat S T (2 • z)) vac := by
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hy := smul_finRat_mem hψ hcc gS hLS hLT hS hT P c (nsmul_mem hz 2)
  have hl : (1 - e) • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    GlobalTheory.AdTh.MovedSum.one_sub_smul_mem_latO_pow S T _ _ e P he _ fun s hs => ⟨∑ w ∈ P, c w,
      smul_finRat_mem hψ hcc gS hLS hLT hS hT P c hz _ (by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Ideal.prod_mem_prod fun w hw => Ideal.pow_mem_pow (hs w hw) _)⟩
  have e0 : cA D e • (1 - e) • GlobalTheory.VacUnique.finRat S T z = cA D e • GlobalTheory.VacUnique.finRat S T z := by
    rw [smul_smul, mul_sub, mul_comm (cA D e) e, he.2, sub_zero, mul_one]
  have hl' : cA D e • GlobalTheory.VacUnique.finRat S T z ∈ latO S T LS LT (fun _ => True) :=
    e0 ▸ GlobalTheory.PlaceModelSum.idem_smul_latO hee hl
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 (isCoprime_conj he c)
  have hA : ∀ w ∈ AddSubgroup.closure {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E |
      ∃ s ∈ (((D.host.conj • modul P c : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
        (D.host.conj • D.host.conj • modul P c : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank), w = s • γ},
      ψ (symplO S T (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T w) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨s, hs, γ, hγ, rfl⟩ := hw
      obtain ⟨b', hb', e1⟩ := mul_mem_of_skew (conj_conj_ne_bot P c) hs (m := a) (by rwa [conj_conj_smul])
      rw [smul_comm, smul_finRat, smul_smul, ← e1, ← smul_finRat, smul_comm]
      exact kill hψ hS hT hy (GlobalTheory.PlaceModelSum.idem_smul_latO hee ((finRat_mem_iff hψ hcc gS hLS hLT hS hT _).2 hγ)) hb'
    | zero => rw [map_zero, smul_zero, smul_zero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [map_add (f := _), smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      have h := AddChar.map_zero_eq_one ψ
      rw [← GlobalTheory.PlaceModel.symplO_zero_left S T (GlobalTheory.VacUnique.finRat S T (2 • z)),
        ← add_neg_cancel (incA D (a : D.host.E) • cA D e • GlobalTheory.VacUnique.finRat S T x), GlobalTheory.PlaceModel.symplO_add_left,
        AddChar.map_add_eq_mul, hx, one_mul] at h
      rwa [map_neg, smul_neg, smul_neg]
  have hB : ψ (symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z))) = 1 := by
    have : (b : D.host.E) + (a : D.host.E) = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 D.host.E) D.host.E) hab
    rw [← one_smul (Formalism.L2.Theta.AE D) (cA D e • GlobalTheory.VacUnique.finRat S T z), ← RingHom.map_one (incA D), ← this,
      RingHom.map_add, add_smul, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, kill hψ hS hT hy hl' hb,
      hA z (skew_mem_closure _ hz), one_mul]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  have hC : symplOH S T (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) =
      -symplO S T (cA D e • GlobalTheory.VacUnique.finRat S T z) (GlobalTheory.VacUnique.finRat S T (2 • z)) := by
    rw [symplOH, two_nsmul ((1 - e) • GlobalTheory.VacUnique.finRat S T z), GlobalTheory.PlaceModel.symplO_add_right,
      GlobalTheory.PlaceModel.symplO_smul, e0, ← GlobalTheory.PlaceModel.symplO_skew, ← two_mul, ← mul_assoc, h2, one_mul]
  have h := GlobalTheory.LatVac.heisO_heisO ψ (e • GlobalTheory.VacUnique.finRat S T (2 • z)) (2 • (1 - e) • GlobalTheory.VacUnique.finRat S T z) vac
  rw [hvac.1 _ hl, hC, AddChar.map_neg_eq_inv, hB, inv_one, one_smul] at h
  rw [h, map_nsmul, smul_comm 2 (1 - e), ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.SkewLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

theorem sum_section {M Q : Type} [AddCommGroup M] [AddCommGroup Q] [Fintype Q] (π : M →+ Q) (Z : Q → M) (hZ : ∀ q, π (Z q) = q)
    (χ : M → ℂ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hker : ∀ x, π x = 0 → χ x = 1) {m : M} (hm : χ m ≠ 1) :
    ∑ q, χ (Z q) = 0 := by
  have h1 : ∀ q, χ (Z (q + π m)) = χ m * χ (Z q) := fun q => by
    have e : Z (q + π m) = (Z (q + π m) - (m + Z q)) + (m + Z q) := by abel
    rw [e, hadd, hker _ (by rw [map_sub, map_add (f := _), hZ, hZ]; abel), one_mul, hadd]
  have h2 : ∑ q, χ (Z q) = χ m * ∑ q, χ (Z q) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (π m)) (fun q => χ (Z q))]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have h3 : (χ m - 1) * ∑ q, χ (Z q) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hm)

variable {D : D7}

theorem pt_mem_iff {δ : ℂ} {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : VC D a d) :
    y ∈ La D (tor0 D ⊤ δ) L L' ↔ ∃ z ∈ YYl D L L', GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d z = y := by
  constructor
  · intro hy
    have h : La D (tor0 D ⊤ δ) L L' ≤ (YYl D L L').toAddSubgroup.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨w, hw, A, hA, rfl⟩
      obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
      exact ⟨((c : D.host.K) : D.host.E) • A, (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) hA,
        GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    exact h hy
  · rintro ⟨z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type} (s : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem reads_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c he _ κ e0 vac he0 hread hvac Tm hTm
  subst hS hT
  have hc := hset.crv
  have hψ := hset.std
  have gS := hset.gS
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hne := conj_ne_bot P c
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hc _ hne
    (by rw [conj_conj_smul]; exact isCoprime_conj he.1 c) S.rank T.rank
  have hN0 : 0 < Ideal.absNorm (D.host.conj • modul P c) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hne)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D S.rank),
      GlobalTheory.SkewLatSD.skewLat_sd D _ T.rank hne, rfl⟩
  obtain ⟨-, -, hIm, -, -, -, hq⟩ := GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hc S.rank T.rank _ kp
  have hrep := GlobalTheory.ThetaConj.repInd_of_thSp D _ _ _ (La0 D (tor0 D ⊤ δ) S.rank T.rank) _ e0 hq
    (fun x hx y hy => hIm _ (GlobalTheory.GalTheta.weilElement_smul_mem_thetaLattice D hG ⊤ δ _ _ x hx) y hy) he0
  have hmem0 := pt_mem_iff (δ := δ) (stdL D S.rank) (stdL D T.rank)
  have hmem2 := pt_mem_iff (δ := δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)
  have hinj := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ (delta_ne_zero hc) S.rank T.rank
  have hkI := fun t ht htΛ hk => inId_of_kill hψ hcc gS hLS hLT hSd hTd he c (t := t) ht htΛ hk
  have hsm := fun z hz => smul_finRat_mem hψ hcc gS hLS hLT hSd hTd P c (z := z) hz
  have hhalf := fun z hz => heisO_eq_half hψ hcc gS hLS hLT hSd hTd he.1 c hvac (z := z) hz
  have hsk := fun z hz m hm => smul_skew_mem (conj_conj_ne_bot P c) (a := S.rank) (d := T.rank) (z := z) hz (m := m) hm
  rw [conj_conj_smul] at hsk
  set I := D.host.conj • modul P c with hI
  set p := GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ S.rank T.rank with hp
  set Y := YYl D (stdL D S.rank) (skewLat D I T.rank) with hY
  set A₁ := La0 D (tor0 D ⊤ δ) S.rank T.rank with hA₁
  set A₂ := La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D I T.rank) with hA₂
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = Ideal.absNorm I ^ (S.rank * T.rank) := by
    rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨m, hm, u, hmu⟩ := exists_add_two he c
  have hz : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ z ∈ Y, ((Quotient.out q : A₂) : VC D S.rank T.rank) - p (2 • z) ∈ A₁ := fun q => by
    obtain ⟨z, hz, ez⟩ := (hmem2 _).1 (Quotient.out q).2
    refine ⟨u • z, Y.smul_mem u hz, (hmem0 _).2 ⟨m • z, hsk z hz m hm, ?_⟩⟩
    rw [← ez, ← map_sub, two_nsmul, ← add_smul, ← mul_two, eq_sub_of_add_eq hmu, sub_smul, one_smul]
  choose z hzY hzq using hz
  have hp2 : ∀ w ∈ Y, p w ∈ A₂ := fun w hw => (hmem2 _).2 ⟨w, hw, rfl⟩
  let π : Y →+ A₂ ⧸ A₁.addSubgroupOf A₂ := (QuotientAddGroup.mk' _).comp
    ((p.comp Y.toAddSubgroup.subtype).codRestrict A₂ fun w => hp2 w w.2)
  have hπ : ∀ q, π ⟨2 • z q, nsmul_mem (hzY q) 2⟩ = q := fun q => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    exact hzq q
  have hπ0 : ∀ w : Y, π w = 0 → GlobalTheory.VacUnique.finRat S T (-w.1) ∈ latO S T LS LT (fun _ => True) := fun w hw => by
    obtain ⟨w', hw', ew⟩ := (hmem0 (p w.1)).1
      ((QuotientAddGroup.eq_zero_iff (N := A₁.addSubgroupOf A₂) (⟨p w.1, hp2 w w.2⟩ : A₂)).1 hw)
    rw [finRat_mem_iff hψ hcc gS hLS hLT hSd hTd, ← hinj ew]
    exact neg_mem hw'
  have hn : ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hfun : cosetFn (cA D e) I (0 : WO S T) = ∑ q, ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ • fun t =>
      ψ (symplO S T t (e • GlobalTheory.VacUnique.finRat S T (2 • -z q))) * halfInd (cA D e) (latO S T LS LT fun _ => True) t := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [cosetFn, halfInd, Matrix.zero_apply, sub_zero]
    by_cases h1 : t ∈ latO S T LS LT (fun _ => True) ∧ IsHalf (cA D e) t
    · have e1 : ∀ y, symplO S T t (e • y) = symplO S T t y := fun y => by
        rw [← cA_cA e, ← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1.2)]
      simp only [e1]
      rw [if_pos h1, mul_one]
      by_cases h2 : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j))
      · rw [if_pos ⟨h1.2, h2⟩, Finset.sum_congr rfl fun q _ =>
          kill_of_inId hψ hcc hLS hLT hSd hTd he h1.2 h2 (hsm _ (nsmul_mem (neg_mem (hzY q)) 2)),
          Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn]
      · rw [if_neg fun h => h2 h.2]
        obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Y, ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T w)) ≠ 1 := by
          by_contra h
          push_neg at h
          exact h2 (hkI t h1.2 h1.1 h)
        have h3 := sum_section π (fun q => ⟨2 • z q, nsmul_mem (hzY q) 2⟩) hπ
          (fun w => ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T (-w.1))))
          (fun x y => by
            rw [Submodule.coe_add, neg_add, map_add (f := _), GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
          (fun x hx => GlobalTheory.LatVac.char_sympl_eq_one hψ hSd hTd h1.1 (hπ0 x hx)) (m := ⟨-w, neg_mem hw⟩)
          (by simpa only [neg_neg] using hw1)
        simp only [smul_neg]
        rw [h3, mul_zero]
    · rw [if_neg h1, mul_zero, mul_zero, if_neg fun h => h1 ⟨(half_mem_iff hcc hLS hLT hSd hTd he t h.1).2 fun i j => (h.2 i j).1, h.1⟩]
  have hv : Tm (halfInd (cA D e) (latO S T LS LT fun _ => True)) = vac := by simpa using hTm.vac
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he.1
  have hTmΦ : Tm (cosetFn (cA D e) I 0) = ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ •
      ∑ q, heisO ψ S T (finPt rfl rfl 1 (2 • z q)) vac := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfun, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) 1 (2 • z q) = GlobalTheory.VacUnique.finRat S T (2 • -z q) := by
      unfold finPt
      congr 1
      refine Matrix.ext fun i j => ?_
      simp
    rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd _ _) _ (fun i j => by
      change cA D (cA D e) * (e * _) = e * _
      rw [cA_cA, ← mul_assoc, hee]), hv, hhalf _ (neg_mem (hzY q)), e1]
  have hR := (reads_sum Finset.univ _ _ fun q =>
    heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hset _ _ hread (2 • z q)).smul ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹
  refine ⟨1, IsRootOne.one, ?_⟩
  rw [hTmΦ]
  convert hR using 1
  have hU : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∀ y, al D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) *
      U D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) e0 y =
        U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (2 • z q)) e0 y := fun q y => by
    have h1 := congrFun (hrep _ (Quotient.out q).2 _ (hp2 _ (nsmul_mem (hzY q) 2)) (hzq q)) y
    obtain ⟨k, hk⟩ := hq _ (hp2 _ (hzY q))
    have h2 : al D (tor0 D ⊤ δ) (p (2 • z q)) = 1 := by
      rw [GlobalTheory.ThetaConj.al_of_qH D _ _ (2 * (2 * k)) (by
        rw [map_nsmul, GlobalTheory.NormSum.Expand.qH_nsmul, hk]; push_cast; ring), zpow_mul]
      norm_num
    simp only [GlobalTheory.ThetaConj.aU, h2, one_mul] at h1
    exact h1
  have hs : ((Real.sqrt ((Ideal.absNorm I : ℝ) ^ (S.rank * T.rank)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) : ℂ))⁻¹ =
        ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ := by
    have h1 : (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) = (Ideal.absNorm I : ℝ) ^ (S.rank * T.rank) := by
      push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype, hidx, hU, Finset.sum_apply]
  rw [← hs]
  simp only [U, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end GlobalTheory.SkewLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_indicator_reads_norm_power_unit_vector : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  first | exact @GlobalTheory.SkewLevel.reads_level | exact GlobalTheory.SkewLevel.reads_level | (intros; apply GlobalTheory.SkewLevel.reads_level <;> assumption)
end

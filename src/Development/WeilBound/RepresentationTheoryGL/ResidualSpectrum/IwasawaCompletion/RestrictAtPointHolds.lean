module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.ExistsIwasawaLeft
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.ExistsUpperUnitaryComplex
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL
open scoped ComplexOrder

namespace PositivityTheory.Rg.Rs.C3.Fl

theorem exists_upper_unitary_complex {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, IsUnit T ∧ (∀ i j : Fin N, j < i → T i j = 0) ∧
      T * g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  let g' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := g
  have hg' : IsUnit g' := hg
  have hinj : Function.Injective fun v => v ᵥ* g' := by
    obtain ⟨u, hu⟩ := hg'
    intro v w hvw
    have := congrArg (fun x => x ᵥ* (u⁻¹ : (Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ)ˣ).1) hvw
    simpa [← hu, vecMul_vecMul] using this
  have hS : (g' * g'ᴴ).PosDef := PosDef.mul_conjTranspose_self g' hinj
  set L := LDL.lowerInv hS with hL
  have hD : LDL.diag hS = L * (g' * g'ᴴ) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hLinj : Function.Injective fun v => v ᵥ* L := by
    intro v w hvw
    have := congrArg (fun x => x ᵥ* ⅟L) hvw
    simpa [vecMul_vecMul] using this
  have hDpos : (L * (g' * g'ᴴ) * Lᴴ).PosDef := hS.mul_mul_conjTranspose_same hLinj
  set d := LDL.diagEntries hS
  have hd : ∀ i, 0 < (d i).re ∧ (d i).im = 0 := by
    intro i
    have := hDpos.diag_pos (i := i)
    rw [← hD] at this
    simp only [LDL.diag, diagonal_apply_eq] at this
    exact ⟨(Complex.pos_iff.1 this).1, (Complex.pos_iff.1 this).2.symm⟩
  let s : (Fin N)ᵒᵈ → ℂ := fun i => (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ)
  let T' : Matrix (Fin N)ᵒᵈ (Fin N)ᵒᵈ ℂ := diagonal s * L
  have hT : T' * (g' * g'ᴴ) * T'ᴴ = 1 := by
    have e1 : T' * (g' * g'ᴴ) * T'ᴴ = diagonal s * LDL.diag hS * diagonal (star s) := by
      rw [hD]; simp only [T', conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]
    rw [e1, LDL.diag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hdi : d i = ((d i).re : ℂ) := Complex.ext rfl (by simp [(hd i).2])
    have hr := (hd i).1
    change (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) * d i * star (((Real.sqrt (d i).re)⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.star_def, Complex.conj_ofReal]
    generalize (d i).re = r at hdi hr ⊢
    rw [hdi]
    have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have hne : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
    rw [Real.sq_sqrt hr.le]
  refine ⟨T', ?_, ?_, ?_⟩
  · have h1 : T' * (g' * (T' * g')ᴴ) = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact ⟨⟨T', _, h1, mul_eq_one_comm.1 h1⟩, rfl⟩
  · intro i j hij
    have h0 : L (OrderDual.toDual i) (OrderDual.toDual j) = 0 := LDL.isLowerTriangular_lowerInv hS hij
    change (diagonal s * L) (OrderDual.toDual i) (OrderDual.toDual j) = 0
    rw [diagonal_mul]
    exact mul_eq_zero_of_right _ h0
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    have : T' * g' * (T' * g')ᴴ = 1 := by
      rw [conjTranspose_mul, ← hT]; simp only [Matrix.mul_assoc]
    exact this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_borel_unitary {N : ℕ} (y : GL (Fin N) (Cinf E)) :
    ∃ (b : GL (Fin N) (Cinf E)) (k : Kinf E N),
      (∀ i j : Fin N, j < i → (b : Matrix (Fin N) (Fin N) (Cinf E)) i j = 0) ∧ y = b * Unitary.toUnits k := by
  classical
  let ev : InfinitePlace E → Cinf E →+* ℂ := fun τ => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) τ
  have hu : ∀ τ, IsUnit ((y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ)) := fun τ =>
    (GeneralLinearGroup.map (ev τ) y).isUnit
  choose T _ hTup hTun using fun τ => exists_upper_unitary_complex _ (hu τ)
  let T' : Matrix (Fin N) (Fin N) (Cinf E) := fun i j τ => T τ i j
  have hev : ∀ τ, T'.map (ev τ) = T τ := fun τ => rfl
  have key : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))) = 1 := by
    have hmap : ∀ τ, (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) *
        star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) = 1 := by
      intro τ
      have e1 : (T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ) = T τ * (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev τ) := by
        rw [Matrix.map_mul, hev]
      have e2 : (star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))).map (ev τ) =
          star ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E))).map (ev τ)) := by
        ext i j; rfl
      rw [Matrix.map_mul, e2, e1]
      exact mem_unitaryGroup_iff.1 (hTun τ)
    ext i j τ
    have := congrFun (congrFun (hmap τ) i) j
    rw [Matrix.map_apply] at this
    change ((T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) i j) τ = _
    refine this.trans ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : T' * ((y : Matrix (Fin N) (Fin N) (Cinf E)) * star (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))) = 1 := by
    rw [← Matrix.mul_assoc, key]
  let U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ := ⟨T', _, h1, mul_eq_one_comm.1 h1⟩
  have hk : T' * (y : Matrix (Fin N) (Fin N) (Cinf E)) ∈ Matrix.unitaryGroup (Fin N) (Cinf E) :=
    mem_unitaryGroup_iff.2 key
  refine ⟨U⁻¹, ⟨_, hk⟩, ?_, ?_⟩
  · have hT : T'.BlockTriangular id := fun i j hij => funext fun τ => hTup τ i j hij
    have : Invertible T' := U.invertible
    have hinv := blockTriangular_inv_of_blockTriangular hT
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact hinv hij
  · refine Units.ext ?_
    change (y : Matrix (Fin N) (Fin N) (Cinf E)) =
      ((U⁻¹ : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (T' * (y : Matrix (Fin N) (Fin N) (Cinf E)))
    rw [← Matrix.mul_assoc]
    change _ = ((U⁻¹ * U : (Matrix (Fin N) (Fin N) (Cinf E))ˣ) : Matrix (Fin N) (Fin N) (Cinf E)) * (y : Matrix (Fin N) (Fin N) (Cinf E))
    rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem sum_castLE_eq {c : ℕ} (d : Fin c → ℕ) {m : ℕ} (hm : m ≤ c) :
    ∑ x : Fin m, d (Fin.castLE hm x) = ∑ k ∈ Finset.range m, (if h : k < c then d ⟨k, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < c then d ⟨k, h⟩ else 0) m]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dite_eq_left (lt_of_lt_of_le x.2 hm)]
  rfl

theorem blk_lt_stdBlocks {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) {i j : Fin N}
    (hij : blk (stdBlocks n h) j < blk (stdBlocks n h) i) : j < i := by
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks n h).surjective j
  simp only [blk_apply] at hij
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, sum_castLE_eq, sum_castLE_eq]
  have h1 : ∑ k ∈ Finset.range (b + 1), (if h : k < c then n ⟨k, h⟩ else 0) ≤
      ∑ k ∈ Finset.range a, (if h : k < c then n ⟨k, h⟩ else 0) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hij)
  rw [Finset.sum_range_succ, dite_eq_left b.2] at h1
  simp only [Fin.eta] at h1
  have h2 : (j' : ℕ) < n b := j'.2
  omega

theorem mem_parab_of_upper (R : Type) [CommRing R] {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) {g : GL (Fin N) R}
    (hg : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) R) i j = 0) : g ∈ parab R (stdBlocks n h) :=
  mem_parab.2 fun i j hij => hg i j (blk_lt_stdBlocks n h hij)

end PositivityTheory.Rg.Rs.C3.Fl

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N)

theorem infGL_leviEmb (m : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) m) = leviEmb (Ad E) (stdBlocks n h) fun i => infGL E (n i) (m i) :=
  cornerGL_leviEmb _ _ m

theorem infGL_mem_unipRad {u : GL (Fin N) (Cinf E)} (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) :
    infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) :=
  cornerGL_mem_unipRad _ _ hu

theorem exists_iwasawa (g : GA E N) :
    ∃ (m : ∀ i, GA E (n i)) (u : GA E N) (k : Kinf E N) (g0 : GL (Fin N) (Af E)),
      u ∈ unipRad (Ad E) (stdBlocks n h) ∧
        g = leviEmb (Ad E) (stdBlocks n h) m * u * (infGL E N (Unitary.toUnits k) * finGL E N g0) := by
  obtain ⟨b, k, hb, hy⟩ := exists_borel_unitary (GeneralLinearGroup.map (pInf E) g)
  have hbp : b ∈ parab (Cinf E) (stdBlocks n h) := mem_parab_of_upper _ h hb
  have hlevi : ∀ (z : ∀ i, GL (Fin (n i)) (Cinf E)),
      leviEmb (Cinf E) (stdBlocks n h) z ∈ parab (Cinf E) (stdBlocks n h) := by
    intro z
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb]
    simp [Matrix.blockDiagonal', hab.ne']
  let P : parab (Cinf E) (stdBlocks n h) := ⟨b, hbp⟩
  let L : parab (Cinf E) (stdBlocks n h) :=
    ⟨leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) P),
      hlevi _⟩
  let U := L⁻¹ * P
  have hu : (U : GL (Fin N) (Cinf E)) ∈ unipRad (Cinf E) (stdBlocks n h) := by
    refine Subgroup.mem_map.2 ⟨U, ?_, rfl⟩
    change leviProj (Cinf E) (stdBlocks n h) U = 1
    rw [show U = L⁻¹ * P from rfl, map_mul, map_inv]
    have : leviProj (Cinf E) (stdBlocks n h) L = leviProj (Cinf E) (stdBlocks n h) P := by
      funext a
      ext i j
      simp [L, leviProj, diagBlock, leviEmb, Matrix.blockDiagonal'_apply_eq]
    rw [this, inv_mul_cancel]
  have hbu : b = leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) P) * (U : GL (Fin N) (Cinf E)) := by
    simp [U, L, P]
  let u : GL (Fin N) (Cinf E) := U
  generalize leviProj (Cinf E) (stdBlocks n h) ⟨b, hbp⟩ = M at hbu
  change b = _ at hbu
  refine ⟨fun i => infGL E (n i) (M i), infGL E N u, k, GeneralLinearGroup.map (pFin E) g,
    infGL_mem_unipRad h hu, ?_⟩
  conv_lhs => rw [← infGL_mul_finGL g, hy, hbu]
  rw [map_mul, map_mul, infGL_leviEmb, mul_assoc]

theorem exists_iwasawa_left (g : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (x : GL (Fin N) (Af E)),
      g = u * (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N x)) := by
  obtain ⟨m, u, k, x, hu, e⟩ := exists_iwasawa h g
  refine ⟨leviEmb (Ad E) (stdBlocks n h) m * u * (leviEmb (Ad E) (stdBlocks n h) m)⁻¹,
    ?_, m, k, x, ?_⟩
  · let P : parab (Ad E) (stdBlocks n h) :=
      ⟨leviEmb (Ad E) (stdBlocks n h) m, by
        apply mem_parab_iff.2
        intro a b i j hab
        simp [leviEmb]
        simp [Matrix.blockDiagonal', hab.ne']⟩
    obtain ⟨U, hU, hUeq⟩ := Subgroup.mem_map.1 hu
    rw [← hUeq]
    change ((P * U * P⁻¹ : parab (Ad E) (stdBlocks n h)) : GL (Fin N) (Ad E)) ∈ _
    refine Subgroup.mem_map.2 ⟨P * U * P⁻¹, ?_, ?_⟩
    · change leviProj (Ad E) (stdBlocks n h) (P * U * P⁻¹) = 1
      have hU' : leviProj (Ad E) (stdBlocks n h) U = 1 := hU
      simp [hU']
    · rfl
  · rw [e]
    simp only [mul_assoc, inv_mul_cancel_left]

end PositivityTheory.Rg.Rs.C3.Fl

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Rap

open PositivityTheory.RSHS.LS PositivityTheory.Rg.Rs.C3.Fl

theorem restrictAtPoint_holds : RestrictAtPoint := by
  intro E _ _ _ N c n h π w X _ _ ρ F hF
  obtain ⟨v0, hv0⟩ : ∃ v, F.1 v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hF (LinearMap.ext hc)
  obtain ⟨g0, hg0⟩ : ∃ g, (F.1 v0).1 g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv0 (Subtype.ext (funext hc))
  obtain ⟨u, hu, m0, k, x, rfl⟩ := exists_iwasawa_left h g0
  let xw := Matrix.GeneralLinearGroup.map (pLoc E w) x
  let xo := x * (locGL E N w xw)⁻¹
  have hxo : Matrix.GeneralLinearGroup.map (pLoc E w) xo = 1 := by
    simp only [xo, map_mul, map_inv, pLoc_locGL]
    exact mul_inv_cancel _
  have hx : x = xo * locGL E N w xw := by simp [xo]
  let Lf : X → ((∀ i, GA E (n i)) → ℂ) := fun v m =>
    (F.1 v).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N xo))
  let L : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
    { toFun := Lf
      map_add' := fun v v' => by
        funext m
        simp only [Lf, map_add (f := _)]
        rfl
      map_smul' := fun z v => by
        funext m
        simp only [Lf, map_smul]
        rfl }
  refine ⟨L, fun v => (F.2.1 v).2.2.2 k xo, ?_, ?_⟩
  · intro h0
    apply hg0
    have h1 := congrFun (LinearMap.congr_fun h0 (ρ xw v0)) m0
    change (F.1 (ρ xw v0)).1 _ = 0 at h1
    rw [F.2.2 xw v0] at h1
    change (F.1 v0).1 (_ * finGL E N (locGL E N w xw)) = 0 at h1
    have hfx : finGL E N x = finGL E N xo * finGL E N (locGL E N w xw) := by rw [← map_mul, ← hx]
    rw [(F.2.1 v0).1 u hu, hfx]
    simpa only [mul_assoc] using h1
  · intro p v
    funext m
    have hemb (g : Levi (w.adicCompletion E) (fun i => Fin (n i))) :
        leviEmb _ (stdBlocks n h) g ∈ parab (w.adicCompletion E) (stdBlocks n h) := by
      apply mem_parab_iff.2
      intro a b i j hab
      letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
    let Lp : parab (w.adicCompletion E) (stdBlocks n h) :=
      ⟨leviEmb _ _ (leviProj _ _ p), hemb _⟩
    have hdec : ∃ up ∈ unipRad (w.adicCompletion E) (stdBlocks n h),
        (p : GL (Fin N) (w.adicCompletion E)) =
          leviEmb _ (stdBlocks n h) (leviProj _ (stdBlocks n h) p) * up := by
      refine ⟨((Lp⁻¹ * p : parab (w.adicCompletion E) (stdBlocks n h)) : GL _ _),
        (coe_mem_unipRad _ _).2 ?_, ?_⟩
      · rw [map_mul, map_inv]
        have hproj : leviProj _ (stdBlocks n h) Lp = leviProj _ (stdBlocks n h) p := by
          funext a
          ext i j
          simp [Lp, leviProj, diagBlock, leviEmb, Matrix.blockDiagonal'_apply_eq]
        rw [hproj, inv_mul_cancel]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (mul_inv_cancel_left _ _).symm
    obtain ⟨up, hup, hp⟩ := hdec
    change (F.1 (ρ p v)).1 _ = (F.1 v).1 _
    rw [F.2.2 p v]
    change (F.1 v).1 (_ * finGL E N (locGL E N w (p : GL (Fin N) (w.adicCompletion E)))) = _
    let M' : ∀ i, GA E (n i) := fun i =>
      finGL E (n i) (locGL E (n i) w (leviProj (w.adicCompletion E) (stdBlocks n h) p i))
    have hq : finGL E N (locGL E N w p) =
        leviEmb (Ad E) (stdBlocks n h) M' * finGL E N (locGL E N w up) := by
      rw [hp, map_mul, map_mul]
      congr 1
      exact iota_leviEmb h _
    have hu' : finGL E N (locGL E N w up) ∈ unipRad (Ad E) (stdBlocks n h) := iota_mem_unipRad h hup
    have hcomm : infGL E N (Unitary.toUnits k) * finGL E N xo * finGL E N (locGL E N w p) =
        finGL E N (locGL E N w p) * (infGL E N (Unitary.toUnits k) * finGL E N xo) := by
      rw [mul_assoc, ← map_mul (finGL E N) xo, ← locGL_commute w xo _ hxo, map_mul, ← mul_assoc, infGL_comm, mul_assoc]
    have key : ∀ a b c' d : GA E N, a * (b * c' * d) = (a * b * c' * (a * b)⁻¹) * (a * b * d) := by
      intros
      group
    have hpar : leviEmb (Ad E) (stdBlocks n h) (m * M') ∈ parab (Ad E) (stdBlocks n h) := by
      generalize m * M' = g
      apply mem_parab_iff.2
      intro a b i j hab
      letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
    have hconj : leviEmb (Ad E) (stdBlocks n h) (m * M') *
        finGL E N (locGL E N w up) * (leviEmb (Ad E) (stdBlocks n h) (m * M'))⁻¹ ∈
        unipRad (Ad E) (stdBlocks n h) := by
      obtain ⟨U, hU, hUeq⟩ := Subgroup.mem_map.1 hu'
      let P : parab (Ad E) (stdBlocks n h) := ⟨_, hpar⟩
      let V : parab (Ad E) (stdBlocks n h) := U
      have hkernel : leviProj (Ad E) (stdBlocks n h) V = 1 := MonoidHom.mem_ker.1 hU
      rw [← hUeq]
      change ((P * V * P⁻¹ : parab (Ad E) (stdBlocks n h)) : GL (Fin N) (Ad E)) ∈ _
      rw [coe_mem_unipRad, map_mul, map_mul, map_inv, hkernel, mul_one, mul_inv_cancel]
    rw [mul_assoc, hcomm, hq, key, ← map_mul, (F.2.1 v).1 _ hconj]
    rfl

end PositivityTheory.Rg.Rs.C3.Rap

end

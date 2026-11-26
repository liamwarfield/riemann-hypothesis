module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.ValuationOneApplyLe

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.ValuationLeOneOfNabsLt
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Imports
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.OpenBump
open GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.CellA

private theorem perm_matrix_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (z : GL (Fin N) k)
    (i j : Fin N) :
    (((pm k w)⁻¹ * z * pm k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (z : Matrix (Fin N) (Fin N) k) (w i) (w j) := by
  change (((GroundTheory.Automorphic.permGL k w)⁻¹ * z *
    GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = _
  rw [← map_inv, Units.val_mul, Units.val_mul,
    GroundTheory.Automorphic.mul_permGL_apply, GroundTheory.Automorphic.permGL_mul_apply]
  simp

private theorem pm_wOpen_conj_mem_unipB_of_mem_unipRadLower {k : Type} [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {z : GL (Fin N) k} (hz : z ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * z * pm k (wOpen d hd) ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  rw [mem_unipRadLower] at hz
  obtain ⟨hlow, hdiag⟩ := hz
  rw [mem_parabLower_iff] at hlow
  have hmono := Tuple.monotone_sort (wKey d hd)
  have hanti : ∀ i j : Fin N, j ≤ i →
      blk (stdBlocks d hd) (wOpen d hd i) ≤ blk (stdBlocks d hd) (wOpen d hd j) := by
    intro i j hji
    have := Prod.Lex.monotone_fst _ _ (hmono hji)
    simpa [wKey, wOpen] using this
  constructor
  · intro i j hji
    rw [perm_matrix_conj_apply]
    obtain ⟨⟨a, p⟩, hp⟩ : ∃ x, stdBlocks d hd x = wOpen d hd i := ⟨_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨⟨b, q⟩, hq⟩ : ∃ x, stdBlocks d hd x = wOpen d hd j := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hab := hanti i j hji.le
    rw [← hp, ← hq] at hab
    simp only [blk, Equiv.symm_apply_apply] at hab
    rw [← hp, ← hq]
    rcases lt_or_eq_of_le hab with hlt | rfl
    · exact hlow a b p q hlt
    · rw [hdiag]
      have hpq : p ≠ q := by
        intro hpq
        subst hpq
        have hij : wOpen d hd i = wOpen d hd j := by rw [← hp, ← hq]
        exact absurd ((wOpen d hd).injective hij) (ne_of_gt hji)
      exact Matrix.one_apply_ne hpq
  · intro i
    rw [perm_matrix_conj_apply]
    obtain ⟨⟨a, p⟩, hp⟩ : ∃ x, stdBlocks d hd x = wOpen d hd i := ⟨_, Equiv.apply_symm_apply _ _⟩
    rw [← hp, hdiag]
    exact Matrix.one_apply_eq p

theorem exists_bump (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (hρ : IsSmooth ρ) (v : W) :
    ∃ n : ℕ, 1 ≤ n ∧
      (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ congruenceSubgroup k N n → whitChar ψ N ⟨l, hl⟩ = 1) ∧
      IsCompact ((unipU k d hd ⊓ (congruenceSubgroup k N n).comap
        (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) ∧
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        ((unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k))) ∧
      ∃ f ∈ openFns d hd ρ,
        (∀ u ∈ (unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)),
            f.1.1 (pm k (wOpen d hd) * u) = v) ∧
        ∀ u ∈ unipU k d hd, u ∉ (unipU k d hd ⊓ (congruenceSubgroup k N n).comap
          (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) →
            f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  classical
  obtain ⟨m, hm1, hfix, hwhit⟩ := GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_level ψ hψ d hd ρ hρ v
  have hKo : IsOpen (congruenceSubgroup k N m : Set (GL (Fin N) k)) := isOpen_congruenceSubgroup k N m
  obtain ⟨f, hsupp, hfK⟩ := GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_smInd_bump (parab k (stdBlocks d hd))
    (congruenceSubgroup k N m) hKo _ v hfix
  let f' : IndSp (stdBlocks d hd) ρ :=
    ⟨(ind (parab k (stdBlocks d hd)) ((twist ρ (deltaHalf k fun a => Fin (d a))).comp
      (leviProj k (stdBlocks d hd)))) (pm k (wOpen d hd))⁻¹ f.1,
      smoothPart_stable _ _ _ f.2⟩
  have hf' : ∀ x, f'.1.1 x = f.1.1 (x * (pm k (wOpen d hd))⁻¹) := fun x => rfl
  have hconj : Continuous fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmemL : ∀ u : GL (Fin N) k, u ∈ (unipU k d hd ⊓ (congruenceSubgroup k N m).comap
      (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) ↔
      u ∈ unipU k d hd ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ congruenceSubgroup k N m := by
    intro u
    simp [Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
  have hUcl : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
    have h1 : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) :=
      GlobalTheory.JacInj.isClosed_unipRad (points (Fin N))
    have h2 : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) :=
      GlobalTheory.JacInj.isClosed_unipRad (opp (stdBlocks d hd))
    have h3 := h2.preimage hconj
    have : (unipU k d hd : Set (GL (Fin N) k)) = (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k))) := by
      ext u
      simp [unipU, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
    rw [this]
    exact h1.inter h3
  have hOeq : ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
      (congruenceSubgroup k N m : Set (GL (Fin N) k))) =
      (fun g : GL (Fin N) k => (pm k (wOpen d hd))⁻¹ * g * pm k (wOpen d hd)) ''
        (congruenceSubgroup k N m : Set (GL (Fin N) k)) := by
    ext u
    constructor
    · intro hu
      exact ⟨_, hu, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * y * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ ∈ (congruenceSubgroup k N m : Set (GL (Fin N) k))
      have hy' : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * y * pm k (wOpen d hd)) *
          (pm k (wOpen d hd))⁻¹ = y := by group
      rw [hy']
      exact hy
  have hLset : ((unipU k d hd ⊓ (congruenceSubgroup k N m).comap
      (MulAut.conj (pm k (wOpen d hd))).toMonoidHom : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) =
      ((fun g : GL (Fin N) k => pm k (wOpen d hd) * g * (pm k (wOpen d hd))⁻¹) ⁻¹'
        (congruenceSubgroup k N m : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
    ext u
    rw [SetLike.mem_coe, hmemL]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  refine ⟨m, hm1, hwhit, ?_, ?_, f', ?_, ?_, ?_⟩
  · rw [hLset, hOeq]
    exact ((isCompact_congruenceSubgroup k N m).image
      ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hUcl
  · exact ⟨_, hKo.preimage hconj, hLset.symm⟩
  · show ∀ g : GL (Fin N) k, f'.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
    intro g hg
    rw [hf'] at hg
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hsupp _ hg
    obtain ⟨q, hq, z, _, hzL, hκqz⟩ :=
      GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_parab_mul_lower d hd hm1 hκ
    refine ⟨p * q, Subgroup.mul_mem _ hp hq, _, pm_wOpen_conj_mem_unipB_of_mem_unipRadLower d hd hzL, ?_⟩
    have hg' : g = g * (pm k (wOpen d hd))⁻¹ * pm k (wOpen d hd) := by group
    rw [hg', hpk, hκqz]
    group
  · intro u hu
    rw [hmemL] at hu
    rw [hf']
    exact hfK _ hu.2
  · intro u hu hnot
    rw [hf']
    by_contra hne
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hsupp _ hne
    obtain ⟨q, hq, z, hzK, hzL, hκqz⟩ :=
      GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_parab_mul_lower d hd hm1 hκ
    have hlow : pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
      have := hu
      simp only [unipU, Subgroup.mem_inf, Subgroup.mem_comap] at this
      simpa [MulAut.conj_apply] using this.2
    have hpq : p * q = (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) * z⁻¹ := by
      rw [hpk, hκqz]
      group
    have h1 : p * q = 1 := by
      apply GlobalTheory.CompanionTheory.Rodier.OpenBump.eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd)
      · exact Subgroup.mul_mem _ hp hq
      · rw [hpq]
        exact Subgroup.mul_mem _ hlow (Subgroup.inv_mem _ hzL)
    apply hnot
    rw [hmemL]
    refine ⟨hu, ?_⟩
    have : pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ = z := by
      have := hpq.symm.trans h1
      rw [mul_inv_eq_one] at this
      exact this
    rw [this]
    exact hzK

end PositivityTheory.RgUd.CellA
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.MemUnipUTwo
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

variable {r m : ℕ}

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wConj_apply (u : GL (Fin (r + m)) k) (i j : Fin (r + m)) :
    ((pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ : GL (Fin (r + m)) k) :
      Matrix (Fin (r + m)) (Fin (r + m)) k) i j =
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm i) ((w2 r m).symm j) := by
  rw [wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply]
  rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_unipU_two {u : GL (Fin (r + m)) k} :
    u ∈ unipU k (dd r m) (hdd r m) ↔ u ∈ unipB k (Fin (r + m)) ∧ ∀ i j : Fin (r + m),
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j →
        (i : ℕ) < m ∧ m ≤ (j : ℕ) := by
  set e := stdBlocks (dd r m) (hdd r m) with he
  have hblk : ∀ (a : Fin 2) (i' : Fin (dd r m a)), ((w2 r m).symm (e ⟨a, i'⟩) : ℕ) < m ↔ a = 1 := by
    intro a i'
    have := weyl_shuffle_symm_lt_iff (r := r) (m := m) (e ⟨a, i'⟩)
    rwa [blk_apply] at this
  have hone : ∀ (a b : Fin 2) (i' : Fin (dd r m a)) (j' : Fin (dd r m b)),
      (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨b, j'⟩)) =
        if (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩ then 1 else 0 := by
    intro a b i' j'
    rw [Matrix.one_apply]
    by_cases h : (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (e.injective ((w2 r m).symm.injective h')))]
  constructor
  · intro hu
    refine ⟨hu.1, fun p q hpq => ?_⟩
    have h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈
        unipRadLower k e := hu.2
    obtain ⟨hP, hD⟩ := (mem_unipRadLower k).1 h2
    obtain ⟨⟨a, i'⟩, hi⟩ := e.surjective (w2 r m p)
    obtain ⟨⟨b, j'⟩, hj⟩ := e.surjective (w2 r m q)
    have hp : p = (w2 r m).symm (e ⟨a, i'⟩) := by rw [hi, Equiv.symm_apply_apply]
    have hq : q = (w2 r m).symm (e ⟨b, j'⟩) := by rw [hj, Equiv.symm_apply_apply]
    have hpa := hblk a i'
    have hqb := hblk b j'
    rw [← hp] at hpa
    rw [← hq] at hqb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exfalso
      have h3 := (mem_parabLower_iff k).1 hP a b i' j' hab
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
    · exfalso
      have h3 := hD a i' j'
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, Matrix.one_apply]
      by_cases h : i' = j'
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (by simpa using h'))]
    · have ha : a = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      refine ⟨hpa.2 ha, ?_⟩
      by_contra hq'
      push_neg at hq'
      exact absurd (hqb.1 hq') (by rw [hb]; decide)
  · rintro ⟨hB, hc⟩
    refine ⟨hB, ?_⟩
    show pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e
    refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i' j' hab => ?_, fun a i' j' => ?_⟩
    · rw [wConj_apply]
      have ha : a = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      by_contra hne
      have h1 := hc _ _ (by
        rw [hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
        exact hne)
      have h2 := (hblk a i').1 h1.1
      rw [ha] at h2
      exact absurd h2 (by decide)
    · rw [wConj_apply]
      have hpq : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨a, j'⟩)) =
          (1 : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i' j' := by
        rw [hone, Matrix.one_apply]
        by_cases h' : i' = j'
        · subst h'
          simp
        · rw [if_neg (fun h => h' (by simpa using h)), if_neg h']
      rw [← hpq]
      by_contra hne
      obtain ⟨h1, h2⟩ := hc _ _ hne
      exact absurd ((hblk a j').2 ((hblk a i').1 h1)) (not_lt.2 h2)

end PositivityTheory.RgUd.CellA
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.JTranslate
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Translate
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

theorem translate_apply (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (f : IndSp (stdBlocks d hd) ρ) (u : GL (Fin N) k) :
    (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * u) =
      (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l (f.1.1 (pm k (wOpen d hd) * (a⁻¹ * u * a))) := by
  letI : DecidableEq (Fin h) := Classical.typeDecidableEq _
  have hx : pm k (wOpen d hd) * u * a =
      leviEmb k (stdBlocks d hd) l * (pm k (wOpen d hd) * (a⁻¹ * u * a)) := by
    rw [← hl]
    group
  have hm : leviEmb k (stdBlocks d hd) l ∈ parab k (stdBlocks d hd) :=
    mem_parab_iff.2 fun _ _ i j hab => by
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
  have hp : leviProj k (stdBlocks d hd) ⟨leviEmb k (stdBlocks d hd) l, hm⟩ = l := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hf := f.1.2 ⟨leviEmb k (stdBlocks d hd) l, hm⟩ (pm k (wOpen d hd) * (a⁻¹ * u * a))
  change f.1.1 (pm k (wOpen d hd) * u * a) = _
  rw [hx]
  refine hf.trans ?_
  rw [MonoidHom.comp_apply, hp]
  rfl

theorem translate_mem_openFns (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    {f : IndSp (stdBlocks d hd) ρ} (hf : f ∈ openFns d hd ρ) :
    parInd (stdBlocks d hd) ρ a f ∈ openFns d hd ρ := by
  letI : DecidableEq (Fin h) := Classical.typeDecidableEq _
  have hf' : ∀ g : GL (Fin N) k, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd) := hf
  show ∀ g : GL (Fin N) k, (parInd (stdBlocks d hd) ρ a f).1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
  intro g hg
  obtain ⟨p, hp, n, hn, hpn⟩ := hf' (g * a) hg
  have hm : leviEmb k (stdBlocks d hd) l ∈ parab k (stdBlocks d hd) :=
    mem_parab_iff.2 fun _ _ i j hab => by
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
  refine ⟨p * (leviEmb k (stdBlocks d hd) l)⁻¹,
    (parab k _).mul_mem hp ((parab k _).inv_mem hm), a * n * a⁻¹, haB n hn, ?_⟩
  have hg' : g = p * pm k (wOpen d hd) * n * a⁻¹ := by
    rw [← hpn]
    group
  rw [hg', ← hl]
  group

end General

section Two

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem modExp_two_one (r m : ℕ) : modExp (fun a => Fin (dd r m a)) 1 = -(r : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two, dd]

theorem nabs_pow (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by
  simp [nabs, map_pow]

theorem deltaHalf_levZ (r m : ℕ) (z : kˣ) :
    (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k z ^ (-((m * r : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  have h0 : levZ k r m z 0 = 1 := by simp [levZ] <;> rfl
  have h1 : levZ k r m z 1 = GeneralLinearGroup.scalar (Fin (dd r m 1)) z := by simp [levZ]
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (dd r m 1)) z) = z ^ m := by
    rw [GeneralLinearGroup.det_scalar]
    simp [dd]
  have key : (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 0)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 0 : ℂ) / 2)) *
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 1)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 1 : ℂ) / 2)) := by
    simp only [deltaHalf, Fin.prod_univ_two]
    rfl
  rw [key, h0, h1, hdet, map_one, modExp_two_one, nabs_pow]
  have hx : 0 ≤ nabs k z := by simp [nabs]
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  rw [hn1]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hexp : (((-(r : ℤ) : ℤ) : ℂ) / 2) = (((-(r : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_cpow (pow_nonneg hx m), ← Real.rpow_natCast_mul hx]
  congr 2
  push_cast
  ring

end Two

end PositivityTheory.RgUd.CellA
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem J_translate (ψ : AddChar k Circle) (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ)
    (hV : ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
        (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (L₀ : Subgroup (GL (Fin N) k)) (hL₀U : L₀ ≤ unipU k d hd) (hc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hO : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀)
    (hθ : ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1)
    (F : IndSp (stdBlocks d hd) ρ) (hF : F ∈ openFns d hd ρ) (v : W)
    (hF1 : ∀ u ∈ L₀, F.1.1 (pm k (wOpen d hd) * u) = v)
    (hF0 : ∀ u ∈ unipU k d hd, u ∉ L₀ → F.1.1 (pm k (wOpen d hd) * u) = 0)
    (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    (haU : ∀ u ∈ unipU k d hd, a * u * a⁻¹ ∈ unipU k d hd)
    (haU' : ∀ u ∈ unipU k d hd, a⁻¹ * u * a ∈ unipU k d hd)
    (hstab : ∀ u ∈ L₀, a * u * a⁻¹ ∈ L₀) :
    (J ⟨F, hF⟩ = (vol L₀ : ℂ) • v) ∧
    ∃ hm : parInd (stdBlocks d hd) ρ a F ∈ openFns d hd ρ,
      J ⟨parInd (stdBlocks d hd) ρ a F, hm⟩ = (vol (L₀.map (MulAut.conj a).toMonoidHom) : ℂ) •
        ((deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v) := by
  have hcont : Continuous fun g : GL (Fin N) k => a * g * a⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem1 : ∀ x : GL (Fin N) k, x ∈ L₀.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L₀ := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : a⁻¹ * ((MulAut.conj a).toMonoidHom y) * a = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hy']
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hback : ∀ x : GL (Fin N) k, x = a * (a⁻¹ * x * a) * a⁻¹ := fun x => by group
  refine ⟨?_, PositivityTheory.RgUd.CellA.translate_mem_openFns d hd ρ a l hl haB hF, ?_⟩
  · refine (hV L₀ hL₀U hc hO).2 ⟨F, hF⟩ v ?_ hF0
    intro u hb hu
    rw [hθ u hb hu]
    simpa using hF1 u hu
  · have hL₁U : L₀.map (MulAut.conj a).toMonoidHom ≤ unipU k d hd := by
      intro x hx
      rw [hmem1] at hx
      rw [hback x]
      exact haU _ (hL₀U hx)
    have hL₁c : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) := by
      rw [Subgroup.coe_map]
      exact hc.image hcont
    have hL₁O : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        (L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) := by
      obtain ⟨O, hOo, hOeq⟩ := hO
      have hc2 : Continuous fun g : GL (Fin N) k => a⁻¹ * g * a :=
        (continuous_const.mul continuous_id).mul continuous_const
      refine ⟨(fun g : GL (Fin N) k => a⁻¹ * g * a) ⁻¹' O, hOo.preimage hc2, ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
      rw [hmem1]
      constructor
      · rintro ⟨hxO, hxU⟩
        have : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := ⟨hxO, haU' x hxU⟩
        rw [hOeq] at this
        exact this
      · intro hx
        have hx' : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
          rw [hOeq]
          exact hx
        refine ⟨hx'.1, ?_⟩
        rw [hback x]
        exact haU _ hx'.2
    refine (hV _ hL₁U hL₁c hL₁O).2 _ _ ?_ ?_
    · intro u hb hu
      have hu0 : a⁻¹ * u * a ∈ L₀ := (hmem1 u).1 hu
      have huL₀ : u ∈ L₀ := by
        rw [hback u]
        exact hstab _ hu0
      have key : ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) =
          (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v := by
        rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u, hF1 _ hu0]
      rw [hθ u hb huL₀]
      simpa using key
    · intro u hu hnot
      show ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) = 0
      rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u]
      have hn : a⁻¹ * u * a ∉ L₀ := fun h => hnot ((hmem1 u).2 h)
      rw [hF0 _ (haU' u hu) hn, map_zero, smul_zero]

end PositivityTheory.RgUd.CellA
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Bridge
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace PositivityTheory.RgUd.CellA

@[reducible] def XX (V W : Type) : Fin 2 → Type
  | 0 => V
  | 1 => W

instance instAddCommGroupXX {V W : Type} [AddCommGroup V] [AddCommGroup W] : ∀ a, AddCommGroup (XX V W a)
  | 0 => inferInstanceAs (AddCommGroup V)
  | 1 => inferInstanceAs (AddCommGroup W)

instance instModuleXX {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W] :
    ∀ a, Module ℂ (XX V W a)
  | 0 => inferInstanceAs (Module ℂ V)
  | 1 => inferInstanceAs (Module ℂ W)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def piPair (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) :
    ∀ a : Fin 2, Representation ℂ (GL (Fin (dd r m a)) k) (XX V W a)
  | 0 => A
  | 1 => x

theorem bridge_equiv (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) :
    Nonempty ((prod₂ A x).Equiv (multiProd (stdBlocks (dd r m) (hdd r m)) (piPair A x))) :=
  nonempty_prod₂_equiv_multiProd (k := k) (d := dd r m) (hdd r m) (piPair A x)

section Transport

variable {G V' W' : Type} [Group G] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

theorem twKer_le_comap {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (f : ρ.IntertwiningMap σ)
    (N : Subgroup G) (χ : N →* ℂˣ) : twKer ρ N χ ≤ (twKer σ N χ).comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨n, f v, ?_⟩
  show f (ρ n v - (χ n : ℂ) • v) = _
  rw [map_sub, map_smul, f.isIntertwining]

theorem equiv_apply {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (φ : ρ.Equiv σ) (g : G) (v : V') :
    φ (ρ g v) = σ g (φ v) :=
  LinearMap.congr_fun (φ.isIntertwining' g) v

theorem equiv_mem_twKer {ρ : Representation ℂ G V'} {σ : Representation ℂ G W'} (φ : ρ.Equiv σ)
    (N : Subgroup G) (χ : N →* ℂˣ) (v : V') : φ v ∈ twKer σ N χ ↔ v ∈ twKer ρ N χ := by
  constructor
  · intro h
    have h2 := twKer_le_comap φ.symm.toIntertwiningMap N χ h
    have e : φ.symm (φ v) = v := φ.toLinearEquiv.symm_apply_apply v
    simpa [e] using h2
  · intro h
    exact twKer_le_comap φ.toIntertwiningMap N χ h

end Transport

theorem piPair_levZ (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W)
    (ω : kˣ →* ℂˣ) (hx : HasCentralChar x ω) (z : kˣ) (t : ⨂[ℂ] a, XX V W a) :
    piTensor (piPair A x) (levZ k r m z) t = (ω z : ℂ) • t := by
  have key : piTensor (piPair A x) (levZ k r m z) = (ω z : ℂ) • LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, LinearMap.smul_apply, LinearMap.id_apply]
    have hv : (fun a => piPair A x a (levZ k r m z a) (v a)) = Function.update v 1 ((ω z : ℂ) • v 1) := by
      funext a
      fin_cases a
      · show A (levZ k r m z 0) (v 0) = Function.update v 1 ((ω z : ℂ) • v 1) 0
        have h0 : A (levZ k r m z 0) = 1 := map_one A
        rw [h0, Function.update_of_ne (by decide)]
        rfl
      · show x (levZ k r m z 1) (v 1) = Function.update v 1 ((ω z : ℂ) • v 1) 1
        rw [Function.update_self]
        exact hx z (v 1)
    rw [hv, MultilinearMap.map_update_smul, Function.update_eq_self]
    rfl
  rw [key]
  rfl

theorem nontrivial_piTensor {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  let b := fun a => Module.Basis.ofVectorSpace ℂ (X a)
  have hne : ∀ a, Nonempty (Module.Basis.ofVectorSpaceIndex ℂ (X a)) := fun a => (b a).index_nonempty
  let p : ∀ a, Module.Basis.ofVectorSpaceIndex ℂ (X a) := fun a => (hne a).some
  exact nontrivial_of_ne _ 0 ((Basis.piTensorProduct b).ne_zero p)

theorem exists_not_mem_twKer (ψ : AddChar k Circle) (A : Representation ℂ (GL (Fin r) k) V)
    (x : Representation ℂ (GL (Fin m) k) W) (hA : IsGenericFor ψ A) (hx : IsGenericFor ψ x) :
    ∃ v, v ∉ twKer (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_tensor_product_equiv (piPair A x) (fun a => unipB k (Fin (dd r m a))) (fun a => whitChar ψ (dd r m a))
  have hf : ∀ a, Nontrivial (TwJacquet (piPair A x a) (unipB k (Fin (dd r m a))) (whitChar ψ (dd r m a))) := by
    intro a
    fin_cases a
    · exact hA
    · exact hx
  have := nontrivial_piTensor hf
  have : Nontrivial (TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ)) :=
    e.toEquiv.nontrivial
  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet (piTensor (piPair A x)) (unipM k (dd r m)) (whitM (dd r m) ψ))
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨v, fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)⟩

end PositivityTheory.RgUd.CellA
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker
open GroundTheory.Automorphic.GLnLocal ValuativeRel

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_one_of_nabs_lt (z : kˣ) (hz : nabs k z < 1) : valuation k (z : k) ≤ 1 := by
  have h := (nabs_le_iff z 1).1 (by rw [nabs_one]; exact hz.le)
  simpa using h

theorem scalar_id (t : ℝ) (ht : 0 < t) (i m r : ℕ) :
    (t ^ i) ^ (m * r) * (t ^ i) ^ (-((m * r : ℕ) : ℝ) / 2) = Real.sqrt t ^ (i * m * r) := by
  have hti : 0 < t ^ i := pow_pos ht i
  rw [← Real.rpow_natCast (t ^ i) (m * r), ← Real.rpow_add hti, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)), ← Real.rpow_mul ht.le, ← Real.rpow_natCast t i,
    ← Real.rpow_mul ht.le]
  congr 1
  push_cast
  ring

variable {r m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]


set_option maxHeartbeats 2000000 in
theorem openCellPar (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (ρ : Representation ℂ (Levi k fun a => Fin (dd r m a)) W) (hρ : IsSmooth ρ) (ω : kˣ →* ℂˣ)
    (hcent : ∀ (z : kˣ) (t : W), ρ (levZ k r m z) t = (ω z : ℂ) • t)
    (hv : ∃ v, v ∉ twKer ρ (unipM k (dd r m)) (whitM (dd r m) ψ)) (z : kˣ) (hz : nabs k z < 1) :
    ∃ F : IndSp (stdBlocks (dd r m) (hdd r m)) ρ,
      F ∉ twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) ∧
      ∀ i : ℕ, parInd (stdBlocks (dd r m) (hdd r m)) ρ (aDiag k (r + m) m (z ^ i)) F -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • F ∈
          twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) := by
  obtain ⟨v, hv⟩ := hv
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  have hJ := CellB.openJ k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ
  rcases hJ with ⟨J, vol, -, hJker, hJU, -, hJvol⟩
  have hbump := exists_bump k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ v
  rcases hbump with ⟨n, -, hwhit, hcpt, hopen, f, hf, hfv, hf0⟩
  have hle : CellB.congrL k r m n ≤ unipU k (dd r m) (hdd r m) := inf_le_left
  have hwL : ∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))),
      u ∈ CellB.congrL k r m n → whitChar ψ (r + m) ⟨u, hb⟩ = 1 :=
    fun u hb hu => hwhit u hb (CellB.mem_congrL.1 hu).2
  obtain ⟨hpos, hJf⟩ := hJvol _ hle hcpt hopen
  have hJ0 := hJf ⟨f, hf⟩ v (fun u hb hu => by
    rw [hwL u hb hu, Units.val_one, one_smul]; exact hfv u hu) hf0
  have hz1 := valuation_le_one_of_nabs_lt z hz
  refine ⟨f, ?_, fun i => ?_⟩
  · intro h
    have h2 := (hJker ⟨f, hf⟩).2 h
    rw [hJ0] at h2
    exact hv ((Submodule.smul_mem_iff _ (Complex.ofReal_ne_zero.2 hpos.ne')).1 h2)
  · have hval : valuation k ((z ^ i : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one₀ zero_le' hz1
    set a := aDiag k (r + m) m (z ^ i) with ha
    have hconj := conj_aDiag (r := r) (m := m) k (z ^ i)
    have hB : ∀ u ∈ unipB k (Fin (r + m)), a * u * a⁻¹ ∈ unipB k (Fin (r + m)) :=
      fun u hu => aDiag_conj_mem_unipB k _ m (z ^ i) hu
    have hU : ∀ u ∈ unipU k (dd r m) (hdd r m), a * u * a⁻¹ ∈ unipU k (dd r m) (hdd r m) :=
      fun u hu => aDiag_conj_mem_unipU k (z ^ i) hu
    have hUi : ∀ u ∈ unipU k (dd r m) (hdd r m), a⁻¹ * u * a ∈ unipU k (dd r m) (hdd r m) := by
      intro u hu
      have h := aDiag_conj_mem_unipU (r := r) (m := m) k (z ^ i)⁻¹ hu
      rwa [← aDiag_inv, inv_inv] at h
    have hLc : ∀ u ∈ CellB.congrL k r m n, a * u * a⁻¹ ∈ CellB.congrL k r m n := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := CellB.mem_congrL.1 hu
      exact CellB.mem_congrL.2 ⟨hU u hu1,
        aDiag_conj_mem_congr k _ m (z ^ i) hval n ((mem_unipU_two k).1 hu1).1 hu2⟩
    obtain ⟨_, hm, hJa⟩ := J_translate ψ J vol hJvol _ hle hcpt hopen hwL f hf v hfv hf0
      a (levZ k r m (z ^ i)) hconj hB hU hUi hLc
    set δ : ℂ := ((deltaHalf k (fun a : Fin 2 => Fin (dd r m a)) (levZ k r m (z ^ i)) : ℂˣ) : ℂ)
      with hδ
    have hvol := CellB.vol_conj_aDiag ψ ρ J vol hJU hJvol (fun u => mem_unipU_two k) n (z ^ i) hval
      hwL ⟨_, hm⟩ (δ • ρ (levZ k r m (z ^ i)) v)
      (by rw [hcent]; exact smul_ne_zero (Units.ne_zero _) (smul_ne_zero (Units.ne_zero _) hv0))
      (fun u hu => by
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show a⁻¹ * (a * u' * a⁻¹) * a = u' by group, hfv u' hu'])
      (fun u hu hnu => by
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        rw [hf0 _ (hUi u hu) (fun h => hnu (Subgroup.mem_map.2 ⟨a⁻¹ * u * a, h, by
          show a * (a⁻¹ * u * a) * a⁻¹ = u
          group⟩)), map_zero, smul_zero])
    have hmem : parInd (stdBlocks (dd r m) (hdd r m)) ρ a f -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • f ∈
          openFns (dd r m) (hdd r m) ρ := sub_mem hm (Submodule.smul_mem _ _ hf)
    apply (hJker ⟨_, hmem⟩).1
    have hsplit : J ⟨_, hmem⟩ = J ⟨_, hm⟩ -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • J ⟨f, hf⟩ := by
      rw [← map_smul, ← map_sub]
      rfl
    rw [hsplit, hJa, hJ0, hvol, hcent, hδ, deltaHalf_levZ, nabs_pow]
    convert Submodule.zero_mem _
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
    convert zero_smul ℂ v
    rw [sub_eq_zero, map_pow, Units.val_pow_eq_pow_val, ← Complex.ofReal_pow,
      ← scalar_id (nabs k z) (GlobalTheory.SplitWeil.nabs_pos k z) i m r]
    push_cast
    ring

end PositivityTheory.RgUd.CellA
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.CellA


set_option maxHeartbeats 2000000 in
theorem openCell (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.OpenCell k := by
  intro ψ hψ _ r m V W _ _ _ _ A x ω hA hx hgA hgx hxω z hz
  obtain ⟨φ⟩ := bridge_equiv (k := k) A x
  have hs : ∀ a, IsSmooth (piPair A x a) := fun a => by
    fin_cases a
    · exact hA
    · exact hx
  obtain ⟨F, hF, hi⟩ := openCellPar ψ hψ (piTensor (piPair A x)) (isSmooth_piTensor hs) ω
    (piPair_levZ A x ω hxω) (exists_not_mem_twKer ψ A x hgA hgx) z hz
  have e : φ (φ.symm F) = F := by
    first
      | exact φ.apply_symm_apply F
      | exact φ.toLinearEquiv.apply_symm_apply F
      | simp
  refine ⟨φ.symm F, φ.symm F, fun hmem => hF ?_, 0, fun i _ => ?_⟩
  · have := (equiv_mem_twKer φ _ _ (φ.symm F)).2 hmem
    rw [e] at this
    exact this
  · rw [← equiv_mem_twKer φ]
    change φ.toIntertwiningMap _ ∈ _
    rw [map_sub, map_smul]
    change φ _ - _ • φ _ ∈ _
    rw [equiv_apply, e]
    exact hi i

end PositivityTheory.RgUd.CellA

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymDataOfUnifCongr
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain
namespace UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem apply_mul_KOne {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x)
    {a : GL ι k} (ha : a ∈ KOne k ι) {b : GL ι' k} (hb : b ∈ KOne k ι') (x : Matrix ι ι' k) :
    f (a.val * x * b.val) = f x := by
  obtain ⟨a1, a2⟩ := mem_KO.1 (KOne_le_KO ha)
  obtain ⟨b1, b2⟩ := mem_KO.1 (KOne_le_KO hb)
  by_cases hx : IntM x
  · have e : a.val * x * b.val = x + ((a.val - 1) * x * b.val + x * (b.val - 1)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    rw [e]
    exact hp _ _ ((((mem_KOne.1 ha).mul_intM hx).mul_intM b1).add (hx.mul_maxM (mem_KOne.1 hb)))
  · have h1 : f x = 0 := by_contra fun h => hx (hs _ h)
    rw [h1]
    by_contra h
    have := (a2.mul (hs _ h)).mul b2
    apply hx
    simpa [Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).val] using this

theorem reGL_symm_mem_KOne (e : ι ≃ Y) {d : GL Y k} (hd : d ∈ KOne k Y) : (reGL e).symm d ∈ KOne k ι :=
  mem_KOne.2 fun i j => by simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hd (e i) (e j)

def Near (F G : LatFrame (k := k) (ι := ι) (Y := Y)) : Prop :=
  G.ord = F.ord ∧ F.bas⁻¹ * G.bas ∈ KOne k Y

theorem Near.conj {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G) :
    ∃ d ∈ KOne k ι, ∀ g, G.conj.symm g = d⁻¹ * F.conj.symm g * d := by
  refine ⟨_, reGL_symm_mem_KOne F.ord h.2, fun g => ?_⟩
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, h.1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have : reGL F.ord (F.conj.symm g) = F.bas⁻¹ * g * F.bas := by
    conv_rhs => rw [← F.conj.apply_symm_apply g, LatFrame.conj_apply]
    group
  rw [this]; group

theorem Near.J_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G)
    (P : TypeDatum (k := k) (a := ι)) :
    (P.toLevel.map G.conj).J = (P.toLevel.map F.conj).J := by
  obtain ⟨d, hd, e⟩ := h.conj
  ext g
  rw [Level.mem_map, Level.mem_map, e, P.J.mul_mem_cancel_right (P.KOne_le hd),
    P.J.mul_mem_cancel_left (inv_mem (P.KOne_le hd))]

theorem Near.stabLat_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G) :
    stabLat G.bas = stabLat F.bas := by
  ext g
  have hd := KOne_le_KO h.2
  have e : G.bas⁻¹ * g * G.bas = (F.bas⁻¹ * G.bas)⁻¹ * (F.bas⁻¹ * g * F.bas) * (F.bas⁻¹ * G.bas) := by group
  rw [mem_stabLat, mem_stabLat, e, (KO k Y).mul_mem_cancel_right hd, (KO k Y).mul_mem_cancel_left (inv_mem hd)]

theorem Near.transport_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)}
    {F' G' : LatFrame (k := k) (ι := ι') (Y := Y')} (h : Near F G) (h' : Near F' G')
    {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x) :
    G.transport G' f = F.transport F' f := by
  funext x
  change f (G.coords G' x) = f (F.coords F' x)
  rw [← apply_mul_KOne hs hp (reGL_symm_mem_KOne F.ord (inv_mem h.2)) (reGL_symm_mem_KOne F'.ord h'.2) (F.coords F' x)]
  congr 1
  unfold LatFrame.coords
  rw [reGL_symm_val, reGL_symm_val, submatrix_mul_equiv, submatrix_mul_equiv, h.1, h'.1]
  congr 1
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.bas.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc F'.bas.val, Units.mul_inv,
    Matrix.one_mul]

theorem near_refl (F : LatFrame (k := k) (ι := ι) (Y := Y)) : Near F F := ⟨rfl, by simp⟩

theorem val_pow_sub_one {u : k} (hu : valuation k (u - 1) < 1) (m : ℕ) : valuation k (u ^ m - 1) < 1 := by
  have h1 : valuation k u ≤ 1 := by
    have := Valuation.map_add_le (valuation k) hu.le (le_of_eq (map_one (valuation k)))
    simpa using this
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u ^ (m + 1) - 1 = u * (u ^ m - 1) + (u - 1) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ hu
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le ih

variable {ϖ ϖ' : kˣ}

theorem val_div_sub_one (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k ((ϖ : k)⁻¹ * ϖ' - 1) < 1 := by
  have e : (ϖ : k)⁻¹ * ϖ' - 1 = (ϖ : k)⁻¹ * ((ϖ' : k) - ϖ) := by field_simp
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, map_mul, map_inv₀, inv_mul_lt_one₀ h0]

theorem near_typeFrame {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) (o : ι ≃ n ⊕ Fin c) :
    Near (typeFrame ϖ o) (typeFrame ϖ' o) := by
  have frameVal (u : kˣ) : (typeFrame u o).bas.val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (u : k) ^ (i.val + 1)) := by
    change fromBlocks 1 0 0 (diagonal _) = _
    rw [← fromBlocks_diagonal]
    simp
  have frameInvVal : ((typeFrame ϖ o).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [frameVal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rcases i with i | i <;> simp
  refine ⟨rfl, mem_KOne.2 fun i j => ?_⟩
  rw [Units.val_mul, frameInvVal, frameVal, diagonal_mul_diagonal, ← diagonal_one, diagonal_sub, diagonal_apply]
  split_ifs
  · rcases i with i | i
    · simp
    · have := val_pow_sub_one (val_div_sub_one h) (i.val + 1)
      rwa [mul_pow, inv_pow] at this
  · simp

theorem val_eq (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (ϖ' : k) = valuation k (ϖ : k) := Valuation.map_eq_of_sub_lt _ h

theorem isUnif_of_near (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) : IsUnif ϖ' :=
  fun x => by rw [val_eq h]; exact hϖ x

theorem inv_sub_inv_mem (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := by
  have h1 := (hϖ _).1 (val_div_sub_one h)
  have e : ((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k) = -((ϖ' : k)⁻¹ * ((ϖ : k)⁻¹ * ϖ' - 1)) := by
    simp only [Units.val_inv_eq_inv_val]; field_simp; ring
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, Valuation.map_neg, map_mul, map_inv₀, val_eq h, inv_mul_le_one₀ h0]

theorem psi_inv_mul {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {x : k} (hx : x ∈ 𝒪[k]) :
    ψ ((ϖ'⁻¹ : kˣ) * x) = ψ ((ϖ⁻¹ : kˣ) * x) := by
  have hi : (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x ∈ 𝒪[k] := mul_mem (inv_sub_inv_mem hϖ h) hx
  have e : ((ϖ'⁻¹ : kˣ) : k) * x = (ϖ⁻¹ : kˣ) * x + (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x := by ring
  rw [e, AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), mul_one]

theorem isSymLevel_of_near {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {ρ κ l : ℕ}
    {P : TypeDatum (k := k) (a := Fin κ ⊕ Fin l)}
    (hP : IsSymLevel ψ ϖ ρ P) : IsSymLevel ψ ϖ' ρ P := by
  refine ⟨hP.1, fun g => ?_⟩
  have hg := intM_of_mem_KO (P.le_KO g.2)
  rw [hP.2 g, psi_inv_mul hψ hϖ h, psi_inv_mul hψ hϖ h]
  · refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]
  · unfold simpleSum
    refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem transport_iterPhi (P : TypeDatum (k := k) (a := r)) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    {F G : LatFrame (k := k) (ι := Ix r t (j + 1)) (Y := Y)}
    {F' G' : LatFrame (k := k) (ι := Ix r t j) (Y := Y')} (h : Near F G) (h' : Near F' G') :
    G.transport G' (P.iterPhi t μ hμ j) = F.transport F' (P.iterPhi t μ hμ j) :=
  h.transport_eq h'
    (fun x hx i l => by simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc r t j).symm i) l)
    fun x y hy => TypeDatum.Phi_add _ (hμ _) (x.submatrix (ixSucc r t j) id) (y := y.submatrix (ixSucc r t j) id)
      fun _ _ => hy _ _

end General
end UnifChange

open UnifChange

theorem exists_symData_of_unif_congr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ), valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k) → ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ S'.ρ = S.ρ ∧ S'.P = S.P ∧ S'.μ = S.μ ∧ ∀ (τ : ℕ) (ν : Measure k), (∀ j c h, (S'.T (Fin τ)).Phi j c h = (S.T (Fin τ)).Phi j c h) ∧ (∀ j c h, (S'.T (Fin τ)).entry S'.ψ ν j c h 1 1 = (S.T (Fin τ)).entry S.ψ ν j c h 1 1) ∧ (∀ x₀, (S'.T (Fin τ)).Psi 1 x₀ (S'.y0 (Fin τ)) = (S.T (Fin τ)).Psi 1 x₀ (S.y0 (Fin τ))) ∧ (S'.T (Fin τ)).xiTop (box _ (1 : kˣ)) S'.ψ ν (-1) (Submodule.Quotient.mk (S'.y0 (Fin τ))) = (S.T (Fin τ)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin τ))) := by
  intro k _ _ _ _ _ _ s κ S ϖ' h
  let S' : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  refine ⟨S', rfl, rfl, rfl, rfl, rfl, fun τ ν => ?_⟩
  have hPhi : ∀ j c H, (S'.T (Fin τ)).Phi j c H = (S.T (Fin τ)).Phi j c H := fun j c H =>
    transport_iterPhi S.P S.μ S.tame j (near_typeFrame h _) (near_typeFrame h _)
  have hTop : (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  have hJ : ∀ j c H, ((S'.T (Fin τ)).lev j c H).J = ((S.T (Fin τ)).lev j c H).J := fun j c H =>
    (near_typeFrame h _).J_eq _
  have hB : ∀ j c (H : j + c = s + 1), stabLat ((S'.T (Fin τ)).bas j c H) = stabLat ((S.T (Fin τ)).bas j c H) := fun j c H =>
    (near_typeFrame h (stdOrd (Fin κ) (Fin τ) j c H)).stabLat_eq
  have hy : S'.y0 (Fin τ) - S.y0 (Fin τ) ∈ box (XIx (Fin κ) (Fin τ) (s + 1)) (1 : kˣ) := by
    intro i
    unfold SymData.y0
    rw [← Pi.single_sub, Pi.single_apply]
    split_ifs
    · simpa using inv_sub_inv_mem S.unif h
    · simp
  refine ⟨hPhi, fun j c H => ?_, fun x₀ => ?_, ?_⟩
  · unfold Chain.entry xi volNat
    rw [hPhi, hJ, hB]
    rfl
  · let t := Fin τ
    let rowOrd := stdOrd (Fin κ) t (s + 1) 0 rfl
    let colOrd := stdOrd (Fin κ) t s (0 + 1) rfl
    have coords (u : kˣ) (y : XIx (Fin κ) t (s + 1) → k) :
        (typeFrame u rowOrd).coords (typeFrame u colOrd) (withCol x₀ y) =
          (withCol x₀ ((u : k) • y)).submatrix rowOrd colOrd := by
      have rowBas : (typeFrame u rowOrd).bas = 1 := by
        apply Units.ext
        ext i j
        rcases i with i | i
        · rcases j with j | j
          · simp [typeFrame, embA, Matrix.one_apply]
          · exact j.elim0
        · exact i.elim0
      unfold LatFrame.coords
      rw [rowBas]
      congr 1
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
        · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
      · exact i.elim0
    have scaled : (ϖ' : k) • S'.y0 t = (S.ϖ : k) • S.y0 t := by
      ext i
      simp only [SymData.y0, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp [S']
    simp only [Chain.Psi, om_one, SymData.T, typeChain, Chain.ofType, LatFrame.transport]
    rw [coords ϖ', coords S.ϖ, scaled]
  · unfold Chain.xiTop
    rw [hTop, (Submodule.Quotient.eq _).2 hy]

end GlobalTheory.SymChain
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.Fam.MidLoc
open _root_.Formalism.L2.Col (IntAt redP qOf)

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iter_le {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) {μ μ' : ℕ → kˣ →* ℂˣ}
    (h : ∀ j, IsTame (μ j)) (h' : ∀ j, IsTame (μ' j)) (n : ℕ) (e : ∀ j, 1 ≤ j → j ≤ n → μ j = μ' j) (j : ℕ) (hj : j ≤ n) :
    P.iter t μ h j = P.iter t μ' h' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [TypeDatum.iter_succ, TypeDatum.iter_succ, ih (by omega)]
    have key : ∀ (Q : TypeDatum k (Ix r t j)) (a b : kˣ →* ℂˣ) (ha : IsTame a) (hb : IsTame b), a = b →
        TypeDatum.step t Q a ha = TypeDatum.step t Q b hb := fun Q a b ha hb E => by subst E; rfl
    rw [key _ _ _ (h _) (h' _) (e (j + 1) (by omega) hj)]

theorem withMu_le {s κ : ℕ} (S : SymData k s κ) (μ : ℕ → kˣ →* ℂˣ) (h : ∀ j, IsTame (μ j))
    (e : ∀ j, 1 ≤ j → j ≤ s + 2 → μ j = S.μ j) (t : Type) [Fintype t] [DecidableEq t] :
    ((withMu S μ h).T t).Phi = (S.T t).Phi ∧ ((withMu S μ h).T t).PhiTop = (S.T t).PhiTop ∧
      ((withMu S μ h).T t).lev = (S.T t).lev := by
  have hΦ : ∀ j, j ≤ s + 1 → S.P.iterPhi t μ h j = S.P.iterPhi t S.μ S.tame j := fun j hj => by
    unfold TypeDatum.iterPhi
    rw [iter_le S.P h S.tame (s + 2) e j (by omega), e (j + 1) (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · funext j a ha
    change LatFrame.transport _ _ (S.P.iterPhi t μ h j) = LatFrame.transport _ _ (S.P.iterPhi t S.μ S.tame j)
    rw [hΦ j (by omega)]; rfl
  · change LatFrame.transport _ _ (S.P.iterPhi t μ h _) = LatFrame.transport _ _ (S.P.iterPhi t S.μ S.tame _)
    rw [hΦ _ le_rfl]; rfl
  · funext j a ha
    change (S.P.iter t μ h j).toLevel.map _ = (S.P.iter t S.μ S.tame j).toLevel.map _
    rw [iter_le S.P h S.tame (s + 2) e j (by omega)]; rfl

variable [MeasurableSpace k] [BorelSpace k]

def SameData {s κ : ℕ} (S' S : SymData k s κ) (τ : ℕ) (ν : Measure k) : Prop :=
  (∀ j c h, (S'.T (Fin τ)).entry S'.ψ ν j c h 1 1 = (S.T (Fin τ)).entry S.ψ ν j c h 1 1) ∧
    (∀ x₀, (S'.T (Fin τ)).Psi 1 x₀ (S'.y0 (Fin τ)) = (S.T (Fin τ)).Psi 1 x₀ (S.y0 (Fin τ))) ∧
    (S'.T (Fin τ)).xiTop (box _ (1 : kˣ)) S'.ψ ν (-1) (Submodule.Quotient.mk (S'.y0 (Fin τ))) =
      (S.T (Fin τ)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin τ)))

theorem exists_normal {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ) (h : valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k))
    (τ : ℕ) (ν : Measure k) : ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ (∀ j, j ≤ s + 2 → S'.μ j = S.μ j) ∧
      (∀ j, s + 2 < j → S'.μ j = 1) ∧ SameData S' S τ ν := by
  obtain ⟨S₁, h1, h2, -, -, h5, h6⟩ := exists_symData_of_unif_congr S ϖ' h
  obtain ⟨-, h7, h8, h9⟩ := h6 τ ν
  let μ : ℕ → kˣ →* ℂˣ := fun j => if j ≤ s + 2 then S₁.μ j else 1
  have ht : ∀ j, IsTame (μ j) := fun j => by
    simp only [μ]
    split_ifs
    · exact S₁.tame j
    · exact fun _ _ => rfl
  have e : ∀ j, 1 ≤ j → j ≤ s + 2 → μ j = S₁.μ j := fun j _ hj => if_pos hj
  obtain ⟨w1, w2, w3⟩ := withMu_le S₁ μ ht e (Fin τ)
  refine ⟨withMu S₁ μ ht, h1, h2, fun j hj => (if_pos hj).trans (congrFun h5 j), fun j hj => if_neg (by omega),
    fun j c H => ?_, fun x₀ => ?_, ?_⟩
  · rw [← h7]
    funext x₀
    have hbas : ((withMu S₁ μ ht).T (Fin τ)).bas = (S₁.T (Fin τ)).bas := rfl
    have hψ : (withMu S₁ μ ht).ψ = S₁.ψ := rfl
    simp only [Chain.entry, xi, StepData.flat, GlobalTheory.EntryBridge.om_one_one, w1, w3, hbas, hψ]
  · rw [← h8]
    simp only [Chain.Psi, GlobalTheory.EntryBridge.om_one_one, w1]
    rfl
  · rw [← h9]
    unfold Chain.xiTop
    rw [w2]
    rfl

omit [MeasurableSpace k] [BorelSpace k] in
theorem crd_inl {s κ : ℕ} (S : SymData k s κ) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r s') :
    ∃ d : k, GlobalTheory.EntryBridge.crd S x r s' = d * x r s' ∧ ((∃ a b, r = .inl a ∧ s' = .inl b) → d = 1) := by
  unfold GlobalTheory.EntryBridge.crd LatFrame.coords
  rw [GlobalTheory.SymSupport.typeFrame_inv_val, GlobalTheory.SymSupport.typeFrame_val]
  refine ⟨_, by simp only [typeFrame, submatrix_apply, Equiv.refl_apply, diagonal_mul, mul_diagonal]; exact mul_right_comm _ _ _, ?_⟩
  rintro ⟨a, b, rfl, rfl⟩
  simp


omit [BorelSpace k] in
theorem entry_mul_KOne {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (ν : Measure k) (j c : ℕ) (H : j + 1 + c = s)
    {a : GL (XIx (Fin κ) t (j + 1)) k} (ha : a ∈ KOne k _) {b : GL (XIx (Fin κ) t j) k} (hb : b ∈ KOne k _)
    (x : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k) :
    (S.T t).entry S.ψ ν j c H 1 1 (a.val * x * b.val) = (S.T t).entry S.ψ ν j c H 1 1 x := by
  refine UnifChange.apply_mul_KOne (fun x hx => ?_) (fun x y hy => ?_) ha hb x
  · by_contra hn
    apply hx
    simp only [Chain.entry, xi, StepData.flat, GlobalTheory.EntryBridge.om_one_one, RootEx.opE]
    refine mul_eq_zero_of_right _ (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_))
    have : (S.T t).Phi j (c + 1) (by omega) (affPt 1 x e) = 0 := by
      by_contra h0
      refine hn fun r s' => ?_
      have h1 := GlobalTheory.EntryBridge.phi_supp S t j (c + 1) _ _ h0 (.inl r) (.inl s')
      obtain ⟨d, hd, hd'⟩ := crd_inl S (affPt 1 x e) (.inl r) (.inl s')
      rw [hd, hd' ⟨_, _, rfl, rfl⟩, one_mul] at h1
      simpa [affPt, basePt, Free] using h1
    simp only [this, zero_mul, Pi.zero_apply]
  · simp only [Chain.entry, xi, StepData.flat, GlobalTheory.EntryBridge.om_one_one, RootEx.opE]
    refine congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun e => ?_))
    have e1 : affPt 1 (x + y) e = affPt 1 x e + fromBlocks y 0 0 0 := by
      unfold affPt basePt
      ext (r | r) (s' | s') <;> simp [add_right_comm]
    have e2 : ch (affPt 1 (x + y) e) = ch (affPt 1 x e) := by
      rw [e1]; simp [ch]
    dsimp only
    rw [e2, e1, GlobalTheory.EntryBridge.phi_per]
    intro r s'
    obtain ⟨d, hd, hd'⟩ := crd_inl S (fromBlocks y 0 0 0 : Matrix (_ ⊕ Fin (c + 1)) (_ ⊕ Fin (c + 1 + 1)) k) r s'
    rw [hd]
    rcases r with r | r <;> rcases s' with s' | s'
    · rw [hd' ⟨_, _, rfl, rfl⟩, one_mul]; exact hy r s'
    all_goals simp

end Loc

section Comparison₂
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psi_tie (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hv : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x) (hd : DenseRange (ofSplit q).pr)
    (hp : (qOf PP).Prime) (hsq : ((qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2)
    (hxi : IntAt PP D.host.xi0) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    {K : Type} [Field K] (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 D.host.E ⧸ PP.asIdeal) K)
    (hW : ∀ (z : 𝓞 D.host.E ⧸ PP.asIdeal) (b : ℤ), redP PP D.host.xi0 * z = b →
      σ₀ (ψ₀ z) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf PP : ℂ)))
    (ψk : AddChar k Circle) (hch : (ofSplit q).IsChar ψ ψk) (a : D.host.E) (ha : IntAt PP a) :
    (ψk ((q.pr.comp (incA D)) (a / (qOf PP : D.host.E))) : ℂ) = σ₀ (ψ₀ (redP PP a)) := by
  let ι : D.host.E →+* k := q.pr.comp (incA D)
  obtain ⟨ϖ, hϖ, hu⟩ := LevelData.exists_unif (ι := ι) hi hd hsq
  obtain ⟨r, -, hr0, hr⟩ := GlobalTheory.SymTieExists.exists_residue PP ι hi hd
  have hch' : ∀ y, (ψk y : ℂ) = psiE ψ (q.sec (ι D.host.xi0 * y)) := fun y => (hch y).trans (congrArg _ (LevelData.mul_sec q _ y))
  have hx1 : ι D.host.xi0 ∈ 𝒪[k] := (hi _).2 hxi
  haveI : Finite (𝓞 D.host.E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  letI := Fintype.ofFinite (𝓞 D.host.E ⧸ PP.asIdeal)
  let e := ZMod.ringEquivOfPrime (𝓞 D.host.E ⧸ PP.asIdeal) hp (by
    rw [← Nat.card_eq_fintype_card, qOf, Ideal.absNorm_apply, Submodule.cardQuot_apply])
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (e.symm (redP PP D.host.xi0 * redP PP a))
  have hb' : redP PP D.host.xi0 * redP PP a = b := by rw [← e.apply_symm_apply (_ * _), ← hb, map_intCast]
  have ha1 : ι a ∈ 𝒪[k] := (hi _).2 ha
  have h1 := (hr0 (⟨_, hx1⟩ * ⟨_, ha1⟩ - b)).1 (by rw [map_sub, map_mul, hr, hr, map_intCast, hb', sub_self])
  have h2 : valuation k (ι D.host.xi0 * ι a - b) ≤ valuation k (ϖ : k) := (hu _).1 h1
  rw [hW _ b hb', hch', ← map_mul]
  refine GlobalTheory.SplitDegOneChar.psiE_sec_pr_eq_exp D k q PP _ hp rfl hsq hv hi ψ hψ _ b ((hi _).1 ?_)
  change ι _ ∈ _
  rw [← mul_div_assoc, ← sub_div, map_div₀, ← hϖ, map_sub, map_mul, map_intCast, Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ h2 zero_le

theorem chi_tie (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hid : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x) (hd : DenseRange (ofSplit q).pr)
    (μ : ℕ → (AE D)ˣ →* Circle) (η : (AE D)ˣ →* Circle) (j : ℕ) {H Hη : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (h1 : ChrEq (μ j) H) (h2 : IsRes H PP c⁻¹) (h3 : ChrEq η Hη) (h4 : IsRes Hη PP 1)
    (m : kˣ →* ℂˣ) (hm : (ofSplit q).IsComp (Lift.chrStep μ η j).1⁻¹ m) (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ)
    (ha : IntAt PP a) (hr : (r : Formalism.L2.DIV.kP PP) = redP PP a) (hu : (u : k) = (ofSplit q).pr a) : m u = c r := by
  obtain ⟨ma, hma⟩ := Witness.exists_isComp (ofSplit q) (μ j)
  obtain ⟨mb, hmb⟩ := Witness.exists_isComp (ofSplit q) η
  have e1 := (GlobalTheory.T.splitPoint_heckeComponent_tame_and_residual D k q PP hid hi hd _ _ _ _ h1 h2 hma).2 a u r ha hr hu
  have e2 := (GlobalTheory.T.splitPoint_heckeComponent_tame_and_residual D k q PP hid hi hd _ _ _ _ h3 h4 hmb).2 a u r ha hr hu
  have f0 := hm u (SymChainAt.idl q u) rfl
  have f1 := hma u (SymChainAt.idl q u) rfl
  have f2 := hmb u (SymChainAt.idl q u) rfl
  rw [e1] at f1
  rw [e2] at f2
  refine Units.ext (f0.trans ?_)
  unfold Lift.chrStep
  split_ifs <;> simp [← f1, ← f2]

end Comparison₂

section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]


omit [NumberField E] [StarRing E] in
theorem exists_KOne (ι : E →+* k) {Y : Type} [Fintype Y] [DecidableEq Y] {a n : ℕ} (h : n = a) (F : Frame k n Y) (e : Y ≃ Fin n)
    (hF : F.β = (1 : Matrix (Fin n) (Fin n) k).submatrix id e) (f : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (hf : ∀ r s, valuation k (ι (f (Pi.single s 1) r - if r = s then 1 else 0)) < 1) :
    ∃ g ∈ KOne k Y, g.val = F.γ * Matrix.of fun r c => ι (f (Pi.single (e.trans (finCongr h) c) 1) (finCongr h r)) := by
  subst h
  have hγ : F.γ = (1 : Matrix (Fin n) (Fin n) k).submatrix e id := by
    have : F.β * (1 : Matrix (Fin n) (Fin n) k).submatrix e id = 1 := by
      rw [hF, submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
    calc F.γ = F.γ * (F.β * (1 : Matrix (Fin n) (Fin n) k).submatrix e id) := by rw [this, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  obtain ⟨g, hg, e1⟩ := exists_mul_KOne (g := (1 : GL Y k)) (one_mem _)
    (M := F.γ * Matrix.of fun r c => ι (f (Pi.single (e.trans (finCongr rfl) c) 1) (finCongr rfl r))) fun r c => by
      have := hf (e r) (e c)
      rw [map_sub, apply_ite ι, map_one, map_zero] at this
      convert this using 2
      simp [hγ, Matrix.mul_apply, Matrix.one_apply]
  exact ⟨g, hg, by rw [← e1, one_mul]⟩

theorem toLoc_inFr (ι : E →+* k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {a b nS nT : ℕ} (hS : nS = a)
    (hT : nT = b) (FS : Frame k nS Y') (FT : Frame k nT Y) (e' : Y' ≃ Fin nS) (e : Y ≃ Fin nT)
    (hFS : FS.β = (1 : Matrix (Fin nS) (Fin nS) k).submatrix id e') (hFT : FT.β = (1 : Matrix (Fin nT) (Fin nT) k).submatrix id e)
    (f : (Fin a → E) ≃ₗ[E] (Fin a → E)) (f' : (Fin b → E) ≃ₗ[E] (Fin b → E))
    (hf : ∀ r s, valuation k (ι (f (Pi.single s 1) r - if r = s then 1 else 0)) < 1)
    (hf' : ∀ r s, valuation k (ι (f' (Pi.single s 1) r - if r = s then 1 else 0)) < 1) :
    ∃ g ∈ KOne k Y, ∃ g' ∈ KOne k Y', ∀ z : Matrix (Fin nT) (Fin nS) E,
      toLoc ι (e.trans (finCongr hT)) (e'.trans (finCongr hS))
        (Formalism.L2.Col.inFr f f' (Matrix.toLin' (z.reindex (finCongr hT) (finCongr hS)))) = g.val * (FT.γ * z.map ι * FS.β) * g'.val := by
  obtain ⟨g, hg, e1⟩ := exists_KOne ι hT FT e hFT f' hf'
  obtain ⟨g', hg', e2⟩ := exists_KOne ι hS FS e' hFS f hf
  refine ⟨g⁻¹, inv_mem hg, g', hg', fun z => ?_⟩
  have h := StdMatch.mul_toLoc ι hS hT f f' (e'.trans (finCongr hS)) (e.trans (finCongr hT))
    (Matrix.of fun r c => ι (f (Pi.single (e'.trans (finCongr hS) c) 1) (finCongr hS r)))
    (Matrix.of fun r c => ι (f' (Pi.single (e.trans (finCongr hT) c) 1) (finCongr hT r))) (fun _ _ => rfl) (fun _ _ => rfl) z
  rw [e2, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, Matrix.mul_assoc, ← h,
    ← Matrix.mul_assoc FT.γ, ← e1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

end Mat

section Tuple
open _root_.Formalism.L2.Col

theorem xiAt_tw_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Formalism.L2.DIV.Tup X.F X.E X.K S) (G : ChGlob X R.m)
    (P : rowSG Pr sel mu) (P' : rowSG Pr sel mu') (h : P.1 = P'.1) (hP : P.1 ∈ Pr.vGs) (i : ℕ) :
    XiAt Ch sel mu (twCst Ch sel mu G) i P 1 1 = XiAt Ch sel mu' (twCst Ch sel mu' G) i P' 1 1 := by
  obtain ⟨P, h1⟩ := P
  obtain ⟨P', h2⟩ := P'
  obtain rfl : P = P' := h
  unfold XiAt E1at
  rw [funext (GlobalTheory.SymBridge.PsiStep.omPhi_one_one Ch sel mu _ _ i), funext (GlobalTheory.SymBridge.PsiStep.omPhi_one_one Ch sel mu' _ _ i)]
  unfold PhiAt twCst
  simp only [if_pos hP]
  rfl

end Tuple

section World
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word}


theorem frame_cong (hI : I.Ok) {b : I.ι} {j : ℕ} (p : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup b) u j)
    (hp : TC.PtOf (TC.kStd X u (B.R.N j)) (extTo I.SQ p)) (P : BadPr I b) (hP : P.1 ∈ (B.primes X).vGs) (r s : Fin (B.R.N j)) :
    P.1.valuation B.fields.E (Formalism.L2.Col.frsF I.sel (I.tup b) p P (Pi.single s 1) r - if r = s then 1 else 0) < 1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  have hT := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 (Finset.mem_union_left _ hP)
  have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) (GlobalTheory.BasePrimes.primes_ok B X).1 u (B.R.N j)).2.1 _ hT
  have hb' : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (TC.kStd X u (B.R.N j))⁻¹ = 1 := by
    rw [map_inv, hb, inv_one]
  have h1 : ∀ r s, adAt B.host.F P.1 (((TC.kStd X u (B.R.N j))⁻¹).1 r s) = if r = s then 1 else 0 := fun r s => by
    have he := congrArg (fun g => (g.1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) _) r s) hb'
    simp only [Units.val_one] at he
    rw [AdT.LocSplice.adAt_eq_of_prV P.1 (z' := (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (AfE B.host.F B.host.E)) r s)
      (he.trans (by by_cases h : r = s <;> simp [Matrix.one_apply, h]))]
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  have h2 := AdT.FrameMove.val_sub_lt_of_liftFr hp ⟨P.1, hP⟩ r s
  have e3 : Formalism.L2.Col.frsF I.sel (I.tup b) p P = p.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  rw [e3, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  convert h2 using 2
  have e4 : ∀ y : Fin (B.R.N j) → B.host.E, adAt B.host.F P.1 (GlobalTheory.Mem.Col2.pullV (TC.kStd X u (B.R.N j)) y r) =
      algebraMap B.host.E (P.1.adicCompletion B.host.E) (y r) := fun y => by
    unfold GlobalTheory.Mem.Col2.pullV
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mulVec, dotProduct, map_sum]
    simp only [map_mul, h1, adAt_inclE]
    simp
  refine Eq.trans ?_ (congrArg (· - _) (e4 _).symm)
  refine ((algebraMap B.host.E (P.1.adicCompletion B.host.E)).map_sub _ _).trans (congrArg₂ (· - ·) rfl ?_)
  rw [Matrix.one_apply]
  split_ifs <;> simp

end World

end GlobalTheory.Fam.MidLoc

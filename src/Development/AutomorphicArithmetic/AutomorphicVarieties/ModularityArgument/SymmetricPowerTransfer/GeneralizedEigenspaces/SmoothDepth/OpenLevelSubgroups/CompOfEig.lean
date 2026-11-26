module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ContE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Imports

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompOfEig
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.compOfEig :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w →
                 ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ (iw w).J n → ∀ g, φ (g * x) = φ g) →
                 ∀ ψ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w (iw w) ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := compEx H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, locSub H _ n ψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap (iw w) _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap (iw w) ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap (iw w) ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ImportsAlt
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.raise :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ U : Subgroup (UA L n), U ≤ Kall (L := L) n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall (L := L) n ≤ U ∧ IsUnramU π w) → ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (φ : UA L n → V), φ ≠ 0 → CoefIn φ π →
        IsAF R (lev U S W) φ → ∃ φ' : UA L n → V, φ' ≠ 0 ∧ CoefIn φ' π ∧ IsAF R U φ' := by
  classical
  intro L _ _ _ n V _ _ _ R π hπ U hU S
  induction S using Finset.induction_on with
  | empty => exact fun _ _ W φ h0 hc h => ⟨φ, h0, hc, h.left, h.inf, fun u hu => h.level u (by simpa [lev] using hu)⟩
  | insert w S hw ih =>
    intro hS hK W φ h0 hc h
    have hwm : w ∈ insert w S := Finset.mem_insert_self _ _
    obtain ⟨φ', a0, a1, a2⟩ := spanSph L n V π hπ w (hK w hwm).2 φ h0 hc
    obtain ⟨k1, k2, -⟩ := spanKeep L n V w φ φ' a1
    have hA : IsAF R (lev U S W ⊓ away n w) φ' := k2 R _ inf_le_right ⟨h.left, h.inf, fun u hu => h.level u (by
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
      simp only [lev, away, Subgroup.mem_inf, Subgroup.mem_iInf] at h1 h2 ⊢
      refine ⟨h1.1, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (h2 w' rfl)]; exact one_mem _
      · exact h1.2 w' hw')⟩
    refine ih ⟨fun u hu => hS.split u (Finset.mem_insert_of_mem hu), hS.inj.mono (by simp)⟩
      (fun u hu => hK u (Finset.mem_insert_of_mem hu)) W φ' a0 (k1 π hπ hc) ⟨hA.left, hA.inf, fun u hu g => ?_⟩
    obtain ⟨-, f2, -, -, -, f6⟩ := factor L n w
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 u
    have hxK : x ∈ Kall (L := L) n := ((f6 x hx y hy).1 (hU hu.1)).1
    have hxl : x ∈ lev U S W := by
      simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨(hK w hwm).1 ⟨hx, hxK⟩, fun w' hw' => ?_⟩
      have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun e =>
        hw (hS.inj (Finset.mem_coe.2 hwm) (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw')) e ▸ hw')
      have := (factor L n w').2.2.1 w hne hx
      simp only [away, Subgroup.mem_iInf] at this
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (this w' rfl)]
      exact one_mem _
    have hyl : y ∈ lev U S W := (Subgroup.mul_mem_cancel_left _ hxl).1 hu
    rw [← mul_assoc, hA.level y ⟨hyl, hy⟩, a2 x ⟨hx, hxK⟩]
end

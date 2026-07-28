import Zcash.Circuits.Action.Circuit
import Zcash.Circuits.Integration.SelectorCoherence

/-!
# Action configure selector coherence

Compositional certificates that every selector reference registered by the Orchard
Action configure program was allocated by that same program. Semantic gate
well-formedness is intrinsic to `Gate`; this module supplies the distinct syntactic
selector-allocation invariant.
-/

namespace Zcash.Circuits

open Halo2

set_option maxHeartbeats 20000

namespace AddChip

@[circuit_norm]
theorem addGate_selectorsOwned (cfg : Config) :
    (addGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (a b c : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure a b c) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qAdd => addGate { a, b, c, qAdd })
      (fun qAdd => ({ a, b, c, qAdd } : Config))
      (fun _ => rfl)
      (fun qAdd => addGate_selectorsOwned
        { a, b, c, qAdd })

end AddChip

namespace CondSwap

@[circuit_norm]
theorem swapGate_selectorsOwned (cfg : Config) :
    (swapGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (a b aSwapped bSwapped swap : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure a b aSwapped bSwapped swap) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      a.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qSwap =>
        swapGate
          { qSwap, a, b, aSwapped, bSwapped, swap })
      (fun qSwap =>
        ({ qSwap, a, b, aSwapped, bSwapped, swap } :
          Config))
      (fun _ => rfl)
      (fun qSwap => swapGate_selectorsOwned
        { qSwap, a, b, aSwapped, bSwapped, swap })

end CondSwap

namespace CommitIvk

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qCommitIvk => gate { qCommitIvk, advices })
      (fun qCommitIvk =>
        ({ qCommitIvk, advices } : Config))
      (fun _ => rfl)
      (fun qCommitIvk => gate_selectorsOwned
        { qCommitIvk, advices })

end CommitIvk

namespace Ecc.Add

@[circuit_norm]
theorem gate_selectorsOwned
    (qAdd : Selector)
    (lambda xP yP xQR yQR alpha beta gamma delta :
      Column .advice) :
    (gate qAdd lambda xP yP xQR yQR
      alpha beta gamma delta).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (xP yP xQR yQR lambda alpha beta gamma delta :
      Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (add.configure
        (xP, yP, xQR, yQR, lambda,
          alpha, beta, gamma, delta)) := by
  change Configure.PreservesGateSelectorsAllocated (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAdd ← selector
    createGate
      (gate qAdd lambda xP yP xQR yQR
        alpha beta gamma delta)
    (pure
      ({ qAdd := qAdd, lambda := lambda,
         xP := xP, yP := yP, xQR := xQR,
         yQR := yQR, alpha := alpha,
         beta := beta, gamma := gamma,
         delta := delta } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      xP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yP.toAny) fun _ =>
      Configure.PreservesGateSelectorsAllocated.bind
        (Configure.PreservesGateSelectorsAllocated.enableEquality
          xQR.toAny) fun _ =>
        Configure.PreservesGateSelectorsAllocated.bind
          (Configure.PreservesGateSelectorsAllocated.enableEquality
            yQR.toAny) fun _ =>
          Configure.PreservesGateSelectorsAllocated.selectorCreateGate
            (fun qAdd =>
              gate qAdd lambda xP yP xQR yQR
                alpha beta gamma delta)
            (fun qAdd =>
              ({ qAdd := qAdd, lambda := lambda,
                 xP := xP, yP := yP, xQR := xQR,
                 yQR := yQR, alpha := alpha,
                 beta := beta, gamma := gamma,
                 delta := delta } : Config))
            (fun _ => rfl)
            (fun qAdd => gate_selectorsOwned qAdd
              lambda xP yP xQR yQR
              alpha beta gamma delta)

end Ecc.Add

namespace Ecc.WitnessPoint

@[circuit_norm]
theorem pointGate_selectorsOwned
    (qPoint : Selector) (x y : Column .advice) :
    (pointGate qPoint x y).SelectorsOwned := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.selectorsCovered
        (fun index => decide (index = qPoint.index)) = true)
    [({ name := "x == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice x 0 *
          curveEqn x y } : Constraint Fp),
     ({ name := "y == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice y 0 *
          curveEqn x y } : Constraint Fp)]
  simp [Expression.selectorsCovered, querySelector, queryAdvice,
    curveEqn]

@[circuit_norm]
theorem pointNonIdGate_selectorsOwned
    (qPointNonId : Selector) (x y : Column .advice) :
    (pointNonIdGate qPointNonId x y).SelectorsOwned := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.selectorsCovered
        (fun index =>
          decide (index = qPointNonId.index)) = true)
    [({ name := "on_curve"
        poly := querySelector qPointNonId * curveEqn x y } :
      Constraint Fp)]
  simp [Expression.selectorsCovered, querySelector, queryAdvice,
    curveEqn]

theorem configure_preservesGateSelectorsAllocated
    (x y : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure x y) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.twoSelectorsTwoGates
      (fun qPoint _ => pointGate qPoint x y)
      (fun _ qPointNonId =>
        pointNonIdGate qPointNonId x y)
      (fun qPoint qPointNonId =>
        ({ qPoint, qPointNonId, x, y } : Config))
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun qPoint _ =>
        pointGate_selectorsOwned qPoint x y)
      (fun _ qPointNonId =>
        pointNonIdGate_selectorsOwned qPointNonId x y)

end Ecc.WitnessPoint

namespace Ecc.AddIncomplete

@[circuit_norm]
theorem gate_selectorsOwned
    (qAddIncomplete : Selector)
    (xP yP xQR yQR : Column .advice) :
    (gate qAddIncomplete xP yP xQR yQR).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (xP yP xQR yQR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (add.configure (xP, yP, xQR, yQR)) := by
  change Configure.PreservesGateSelectorsAllocated (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAddIncomplete ← selector
    createGate (gate qAddIncomplete xP yP xQR yQR)
    (pure
      ({ qAddIncomplete := qAddIncomplete,
         xP := xP, yP := yP, xQR := xQR,
         yQR := yQR } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      xP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        xQR.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yQR.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qAddIncomplete =>
        gate qAddIncomplete xP yP xQR yQR)
      (fun qAddIncomplete =>
        ({ qAddIncomplete := qAddIncomplete,
           xP := xP, yP := yP, xQR := xQR,
           yQR := yQR } : Config))
      (fun _ => rfl)
      (fun qAddIncomplete =>
        gate_selectorsOwned qAddIncomplete xP yP xQR yQR)

end Ecc.AddIncomplete

namespace Ecc.Mul

@[circuit_norm]
theorem lsbGate_selectorsOwned (cfg : Config) :
    (lsbGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

end Ecc.Mul

namespace Ecc.MulComplete

@[circuit_norm]
theorem decomposeGate_selectorsOwned (cfg : Config) :
    (decomposeGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (zComplete : Column .advice)
    (addConfig : Ecc.Add.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure zComplete addConfig) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      zComplete.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qDecompose =>
        decomposeGate { qDecompose, zComplete, addConfig })
      (fun qDecompose =>
        ({ qDecompose, zComplete, addConfig } : Config))
      (fun _ => rfl)
      (fun qDecompose =>
        decomposeGate_selectorsOwned
          { qDecompose, zComplete, addConfig })

end Ecc.MulComplete

namespace Ecc.MulOverflow

@[circuit_norm]
theorem overflowGate_selectorsOwned
    (K : ℕ) (cfg : Config K) :
    (overflowGate K cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure K lookupConfig adv0 adv1 adv2) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      adv0.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        adv1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        adv2.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qOverflow =>
        overflowGate K
          { qOverflow, lookupConfig, adv0, adv1, adv2 })
      (fun qOverflow =>
        ({ qOverflow, lookupConfig, adv0, adv1, adv2 } :
          Config K))
      (fun _ => rfl)
      (fun qOverflow =>
        overflowGate_selectorsOwned K
          { qOverflow, lookupConfig, adv0, adv1, adv2 })

end Ecc.MulOverflow

namespace LookupRangeCheck

@[circuit_norm]
theorem bitshiftGate_selectorsOwned
    (K : ℕ) (cfg : Config K) :
    (bitshiftGate K cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (K : ℕ) (runningSum : Column .advice)
    (tableIdx : TableColumn) :
    Configure.PreservesGateSelectorsAllocated
      (configure K runningSum tableIdx) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      runningSum.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.complexComplexSimpleLookupGate
      (fun qLookup qRunning qBitshift =>
        bitshiftGate K
          { qLookup, qRunning, qBitshift,
            runningSum, tableIdx })
      (fun qLookup qRunning qBitshift =>
        ({ qLookup, qRunning, qBitshift,
           runningSum, tableIdx } : Config K))
      (fun _ _ _ =>
        [queryAdvice runningSum 0,
         queryAdvice runningSum 1])
      (fun qLookup qRunning qBitshift =>
        let cfg : Config K :=
          { qLookup, qRunning, qBitshift,
            runningSum, tableIdx }
        [((rangeCheckLookup K cfg).inputs.headI,
          tableIdx)])
      (fun _ _ _ => rfl)
      (fun qLookup qRunning qBitshift =>
        bitshiftGate_selectorsOwned K
          { qLookup, qRunning, qBitshift,
            runningSum, tableIdx })

end LookupRangeCheck

namespace DecomposeRunningSum

@[circuit_norm]
theorem rangeCheckGate_selectorsOwned
    (W : ℕ) (cfg : Config) :
    (rangeCheckGate W cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  selector_free

/--
Relational preservation for the child configure program whose selector is allocated
by its parent.
-/
theorem configure_preservesGateSelectorsAllocated_of_lt
    (W : ℕ) (qRangeCheck : Selector)
    (z : Column .advice) (cs : ConstraintSystem Fp)
    (hcs : cs.GateSelectorsAllocated)
    (hselector : qRangeCheck.index < cs.numSelectors) :
    ConstraintSystem.GateSelectorsAllocated
      (((configure W qRangeCheck z) cs).2) := by
  unfold configure
  simp only [
    Configure.PreservesGateSelectorsAllocated.gateSelectorsAllocated_run_bind,
    Configure.PreservesGateSelectorsAllocated.gateSelectorsAllocated_run_pure]
  let afterEquality :=
    (enableEquality z.toAny cs).2
  change
    ((createGate
      (rangeCheckGate W { qRangeCheck, z })
      afterEquality).2).GateSelectorsAllocated
  rw [ConstraintSystem.gateSelectorsAllocated_createGate]
  constructor
  · exact
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        z.toAny).run cs hcs
  · apply Gate.SelectorsAllocated.of_owned
      (rangeCheckGate_selectorsOwned W
        { qRangeCheck, z })
    simpa [afterEquality] using hselector

@[simp]
theorem configure_numSelectors
    (W : ℕ) (qRangeCheck : Selector)
    (z : Column .advice) (cs : ConstraintSystem Fp) :
    ((configure W qRangeCheck z) cs).2.numSelectors =
      cs.numSelectors := by
  unfold configure
  simp

end DecomposeRunningSum

namespace Sinsemilla.Merkle.Gate

@[circuit_norm]
theorem decomposeGate_selectorsOwned (cfg : Config) :
    (decomposeGate cfg).SelectorsOwned := by
  apply Halo2.Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole :
      Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure aWhole bWhole cWhole leftNode rightNode
        z1A z1B b1 b2 lWhole) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qDecompose =>
        decomposeGate
          (Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
            z1A z1B b1 b2 lWhole))
      (fun qDecompose =>
        Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
          z1A z1B b1 b2 lWhole)
      (fun _ => rfl)
      (fun qDecompose =>
        decomposeGate_selectorsOwned
          (Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
            z1A z1B b1 b2 lWhole))

end Sinsemilla.Merkle.Gate

namespace Sinsemilla.Merkle

theorem configure_preservesGateSelectorsAllocated
    (scfg : HashPiece.Config) :
    Configure.PreservesGateSelectorsAllocated (configure scfg) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (CondSwap.configure_preservesGateSelectorsAllocated
      scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2) fun condSwap =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Gate.configure_preservesGateSelectorsAllocated
        scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
        scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2) fun gate =>
      Configure.PreservesGateSelectorsAllocated.pure
        ({ condSwap, gate, sinsemilla := scfg } : Config)

end Sinsemilla.Merkle

namespace Sinsemilla.HashPiece

@[circuit_norm]
theorem initialYQGate_selectorsOwned (cfg : Config) :
    (initialYQGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [yAExpr, xRExpr, Expression.SelectorFree,
    queryAdvice, queryFixed]

@[circuit_norm]
theorem sinsemillaGate_selectorsOwned (cfg : Config) :
    (sinsemillaGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [yAExpr, xRExpr, qS3Expr,
    Expression.SelectorFree, queryAdvice, queryFixed]

theorem configure_preservesGateSelectorsAllocated
    (G : Specs.Sinsemilla.Generators)
    (xA xP bits lambda1 lambda2 witnessPieces : Column .advice)
    (fixedYQ : Column .fixed)
    (genTable : Sinsemilla.GeneratorTableConfig) :
    Configure.PreservesGateSelectorsAllocated
      (configure G xA xP bits lambda1 lambda2
        witnessPieces fixedYQ genTable) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      xA.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        xP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        bits.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        lambda1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        lambda2.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.complexFixedSimpleLookupTwoGates
      (fun qS1 qS2 qS4 =>
        initialYQGate
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable })
      (fun qS1 qS2 qS4 =>
        sinsemillaGate
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable })
      (fun qS1 qS2 qS4 =>
        ({ qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
           bits, witnessPieces, generatorTable := genTable } : Config))
      (fun qS1 qS2 qS4 =>
        let cfg : Config :=
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable }
        [queryFixed cfg.qS2, queryAdvice cfg.bits 0,
         queryAdvice cfg.bits 1, queryAdvice cfg.xP 0,
         queryAdvice cfg.lambda1 0, queryAdvice cfg.xA 0,
         queryAdvice cfg.lambda2 0])
      (fun qS1 qS2 qS4 =>
        let cfg : Config :=
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable }
        [((generatorLookup G cfg).inputs[0]!, genTable.tableIdx),
         ((generatorLookup G cfg).inputs[1]!, genTable.tableX),
         ((generatorLookup G cfg).inputs[2]!, genTable.tableY)])
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun qS1 qS2 qS4 =>
        initialYQGate_selectorsOwned
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable })
      (fun qS1 qS2 qS4 =>
        sinsemillaGate_selectorsOwned
          { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
            bits, witnessPieces, generatorTable := genTable })

end Sinsemilla.HashPiece

namespace Poseidon

@[circuit_norm]
theorem fullRoundGate_selectorsOwned (cfg : Config) :
    (fullRoundGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [pow5Expr, Expression.SelectorFree,
    queryAdvice, queryFixed]

@[circuit_norm]
theorem partialRoundsGate_selectorsOwned (cfg : Config) :
    (partialRoundsGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [pow5Expr, Expression.SelectorFree,
    queryAdvice, queryFixed]

@[circuit_norm]
theorem padAndAddGate_selectorsOwned (cfg : Config) :
    (padAndAddGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (state : Fin 3 → Column .advice)
    (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    Configure.PreservesGateSelectorsAllocated
      (configure state partialSbox rcA rcB) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      (state 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (state 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (state 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.threeSelectorsThreeGates
      (fun sFull sPartial sPadAndAdd =>
        fullRoundGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        partialRoundsGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        padAndAddGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        ({ state, partialSbox, rcA, rcB,
           sFull, sPartial, sPadAndAdd } : Config))
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun sFull sPartial sPadAndAdd =>
        fullRoundGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        partialRoundsGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        padAndAddGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })

end Poseidon

namespace Ecc.MulIncomplete

@[circuit_norm]
theorem qMul1Gate_selectorsOwned (cfg : Config) :
    (qMul1Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [yA, xRExpr, Expression.SelectorFree, queryAdvice]

@[circuit_norm]
theorem qMul2Gate_selectorsOwned (cfg : Config) :
    (qMul2Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.SelectorFree, queryAdvice]

@[circuit_norm]
theorem qMul3Gate_selectorsOwned (cfg : Config) :
    (qMul3Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (z xA xP yP lambda1 lambda2 : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure z xA xP yP lambda1 lambda2) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      z.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        lambda1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.threeSelectorsThreeGates
      (fun qMul1 qMul2 qMul3 =>
        qMul1Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul2Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul3Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        ({ qMul1, qMul2, qMul3, z, xA, xP, yP,
           lambda1, lambda2 } : Config))
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun qMul1 qMul2 qMul3 =>
        qMul1Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul2Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul3Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })

end Ecc.MulIncomplete

namespace Ecc.Mul

theorem configure_preservesGateSelectorsAllocated
    (addConfig : Ecc.Add.Config)
    (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure addConfig lookupConfig advices) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Ecc.MulIncomplete.configure_preservesGateSelectorsAllocated
      (advices 9) (advices 3) (advices 0) (advices 1)
      (advices 4) (advices 5)) fun hiConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulIncomplete.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 0) (advices 1)
        (advices 8) (advices 2)) fun loConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulComplete.configure_preservesGateSelectorsAllocated
        (advices 9) addConfig) fun completeConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulOverflow.configure_preservesGateSelectorsAllocated
        10 lookupConfig (advices 6) (advices 7)
        (advices 8)) fun overflowConfig =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulLsb =>
        lsbGate
          { qMulLsb, addConfig, hiConfig, loConfig,
            completeConfig, overflowConfig })
      (fun qMulLsb =>
        ({ qMulLsb, addConfig, hiConfig, loConfig,
           completeConfig, overflowConfig } : Config))
      (fun _ => rfl)
      (fun qMulLsb =>
        lsbGate_selectorsOwned
          { qMulLsb, addConfig, hiConfig, loConfig,
            completeConfig, overflowConfig })

end Ecc.Mul

namespace NoteCommit.DecomposeB

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitB =>
        gate { qNotecommitB, colL, colM, colR })
      (fun qNotecommitB =>
        ({ qNotecommitB, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitB => gate_selectorsOwned
        { qNotecommitB, colL, colM, colR })

end NoteCommit.DecomposeB

namespace NoteCommit.DecomposeD

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitD =>
        gate { qNotecommitD, colL, colM, colR })
      (fun qNotecommitD =>
        ({ qNotecommitD, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitD => gate_selectorsOwned
        { qNotecommitD, colL, colM, colR })

end NoteCommit.DecomposeD

namespace NoteCommit.DecomposeE

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitE =>
        gate { qNotecommitE, colL, colM, colR })
      (fun qNotecommitE =>
        ({ qNotecommitE, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitE => gate_selectorsOwned
        { qNotecommitE, colL, colM, colR })

end NoteCommit.DecomposeE

namespace NoteCommit.DecomposeG

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitG =>
        gate { qNotecommitG, colL, colM })
      (fun qNotecommitG =>
        ({ qNotecommitG, colL, colM } : Config))
      (fun _ => rfl)
      (fun qNotecommitG => gate_selectorsOwned
        { qNotecommitG, colL, colM })

end NoteCommit.DecomposeG

namespace NoteCommit.DecomposeH

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitH =>
        gate { qNotecommitH, colL, colM, colR })
      (fun qNotecommitH =>
        ({ qNotecommitH, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitH => gate_selectorsOwned
        { qNotecommitH, colL, colM, colR })

end NoteCommit.DecomposeH

namespace NoteCommit.GdCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitGd =>
        gate { qNotecommitGd, colL, colM, colR, colZ })
      (fun qNotecommitGd =>
        ({ qNotecommitGd, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitGd => gate_selectorsOwned
        { qNotecommitGd, colL, colM, colR, colZ })

end NoteCommit.GdCanonicity

namespace NoteCommit.PkdCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitPkd =>
        gate { qNotecommitPkd, colL, colM, colR, colZ })
      (fun qNotecommitPkd =>
        ({ qNotecommitPkd, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitPkd => gate_selectorsOwned
        { qNotecommitPkd, colL, colM, colR, colZ })

end NoteCommit.PkdCanonicity

namespace NoteCommit.ValueCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitValue =>
        gate { qNotecommitValue, colL, colM, colR, colZ })
      (fun qNotecommitValue =>
        ({ qNotecommitValue, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitValue => gate_selectorsOwned
        { qNotecommitValue, colL, colM, colR, colZ })

end NoteCommit.ValueCanonicity

namespace NoteCommit.RhoCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitRho =>
        gate { qNotecommitRho, colL, colM, colR, colZ })
      (fun qNotecommitRho =>
        ({ qNotecommitRho, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitRho => gate_selectorsOwned
        { qNotecommitRho, colL, colM, colR, colZ })

end NoteCommit.RhoCanonicity

namespace NoteCommit.PsiCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitPsi =>
        gate { qNotecommitPsi, colL, colM, colR, colZ })
      (fun qNotecommitPsi =>
        ({ qNotecommitPsi, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitPsi => gate_selectorsOwned
        { qNotecommitPsi, colL, colM, colR, colZ })

end NoteCommit.PsiCanonicity

namespace NoteCommit.YCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qYCanon => gate { qYCanon, advices })
      (fun qYCanon => ({ qYCanon, advices } : Config))
      (fun _ => rfl)
      (fun qYCanon => gate_selectorsOwned
        { qYCanon, advices })

end NoteCommit.YCanonicity

namespace NoteCommit

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (DecomposeB.configure_preservesGateSelectorsAllocated
      (advices 6) (advices 7) (advices 8)) fun b =>
    Configure.PreservesGateSelectorsAllocated.bind
      (DecomposeD.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8)) fun d =>
    Configure.PreservesGateSelectorsAllocated.bind
      (DecomposeE.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8)) fun e =>
    Configure.PreservesGateSelectorsAllocated.bind
      (DecomposeG.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7)) fun g =>
    Configure.PreservesGateSelectorsAllocated.bind
      (DecomposeH.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8)) fun h =>
    Configure.PreservesGateSelectorsAllocated.bind
      (GdCanonicity.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8) (advices 9)) fun gd =>
    Configure.PreservesGateSelectorsAllocated.bind
      (PkdCanonicity.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8) (advices 9)) fun pkd =>
    Configure.PreservesGateSelectorsAllocated.bind
      (ValueCanonicity.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8) (advices 9)) fun value =>
    Configure.PreservesGateSelectorsAllocated.bind
      (RhoCanonicity.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8) (advices 9)) fun rho =>
    Configure.PreservesGateSelectorsAllocated.bind
      (PsiCanonicity.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 8) (advices 9)) fun psi =>
    Configure.PreservesGateSelectorsAllocated.bind
      (YCanonicity.configure_preservesGateSelectorsAllocated
        advices) fun y =>
    Configure.PreservesGateSelectorsAllocated.pure
      ({ b, d, e, g, h, gd, pkd, value, rho, psi, y } : Config)

end NoteCommit

namespace Ecc.MulFixed.BaseFieldElem

@[circuit_norm]
theorem canonGate_selectorsOwned (cfg : Config) :
    (canonGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  selector_free

theorem configure_preservesGateSelectorsAllocated
    (canonAdvices : Fin 3 → Column .advice)
    (lookupConfig : LookupRangeCheck.Config 10)
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure canonAdvices lookupConfig superConfig) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      (canonAdvices 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (canonAdvices 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (canonAdvices 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedBaseField =>
        canonGate
          { qMulFixedBaseField, canonAdvices,
            lookupConfig, superConfig })
      (fun qMulFixedBaseField =>
        ({ qMulFixedBaseField, canonAdvices,
           lookupConfig, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedBaseField =>
        canonGate_selectorsOwned
          { qMulFixedBaseField, canonAdvices,
            lookupConfig, superConfig })

end Ecc.MulFixed.BaseFieldElem

namespace Ecc.MulFixed.Short

@[circuit_norm]
theorem shortGate_selectorsOwned (cfg : Config) :
    (shortGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  selector_free

theorem configure_preservesGateSelectorsAllocated
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure superConfig) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedShort =>
        shortGate { qMulFixedShort, superConfig })
      (fun qMulFixedShort =>
        ({ qMulFixedShort, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedShort =>
        shortGate_selectorsOwned
          { qMulFixedShort, superConfig })

end Ecc.MulFixed.Short

namespace Ecc.MulFixed.FullWidth

@[circuit_norm]
theorem fullWidthGate_selectorsOwned (cfg : Config) :
    (fullWidthGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  selector_free

theorem configure_preservesGateSelectorsAllocated
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure superConfig) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedFull =>
        fullWidthGate { qMulFixedFull, superConfig })
      (fun qMulFixedFull =>
        ({ qMulFixedFull, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedFull =>
        fullWidthGate_selectorsOwned
          { qMulFixedFull, superConfig })

end Ecc.MulFixed.FullWidth

namespace Ecc.MulFixed

@[circuit_norm]
theorem coordsGate_selectorsOwned (cfg : Config) :
    (coordsGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  selector_free

private theorem configureProgram_preservesGateSelectorsAllocated_of_lt
    (window : Column .advice) (qRunningSum : Selector)
    (cs : ConstraintSystem Fp)
    (hcs : cs.GateSelectorsAllocated)
    (hselector : qRunningSum.index < cs.numSelectors) :
    ((configureProgram window qRunningSum) cs).2.GateSelectorsAllocated := by
  simp only [configureProgram,
    Configure.PreservesGateSelectorsAllocated.gateSelectorsAllocated_run_bind,
    Configure.PreservesGateSelectorsAllocated.gateSelectorsAllocated_run_pure]
  exact Configure.PreservesGateSelectorsAllocated.fixedColumn.run
    ((DecomposeRunningSum.configure 3 qRunningSum window) cs).2
    (DecomposeRunningSum.configure_preservesGateSelectorsAllocated_of_lt
      3 qRunningSum window cs hcs hselector)

private theorem configureProgram_numSelectors
    (window : Column .advice) (qRunningSum : Selector)
    (cs : ConstraintSystem Fp) :
    ((configureProgram window qRunningSum) cs).2.numSelectors =
      cs.numSelectors := by
  simp only [configureProgram, Configure.run_bind_numSelectors]
  have h :=
    DecomposeRunningSum.configure_numSelectors
      3 qRunningSum window cs
  rw [Configure.run_numSelectors] at h
  exact h

private theorem configureTail_preservesGateSelectorsAllocated
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (window u : Column .advice)
    (addConfig : Ecc.Add.Config)
    (addIncompleteConfig : Ecc.AddIncomplete.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configureTail lagrangeCoeffs window u
        addConfig addIncompleteConfig) := by
  unfold configureTail
  exact Configure.PreservesGateSelectorsAllocated.selectorProgramGate
    (configureProgram window)
    (configureGate lagrangeCoeffs window u
      addConfig addIncompleteConfig)
    (configureResult lagrangeCoeffs window u
      addConfig addIncompleteConfig)
    (configureProgram_preservesGateSelectorsAllocated_of_lt window)
    (configureProgram_numSelectors window)
    (fun _ _ => rfl)
    (by
      intro _ _
      apply coordsGate_selectorsOwned)

theorem configure_preservesGateSelectorsAllocated
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (window u : Column .advice)
    (addConfig : Ecc.Add.Config)
    (addIncompleteConfig : Ecc.AddIncomplete.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure lagrangeCoeffs window u addConfig
        addIncompleteConfig) := by
  unfold configure
  apply Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      window.toAny)
  intro _
  apply Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        u.toAny)
  intro _
  exact configureTail_preservesGateSelectorsAllocated
    lagrangeCoeffs window u addConfig addIncompleteConfig

end Ecc.MulFixed

namespace Ecc

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices lagrangeCoeffs rangeCheck) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (WitnessPoint.configure_preservesGateSelectorsAllocated
      (advices 0) (advices 1)) fun witnessPoint =>
    Configure.PreservesGateSelectorsAllocated.bind
      (AddIncomplete.configure_preservesGateSelectorsAllocated
        (advices 0) (advices 1) (advices 2) (advices 3))
        fun addIncomplete =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Add.configure_preservesGateSelectorsAllocated
        (advices 0) (advices 1) (advices 2) (advices 3)
        (advices 4) (advices 5) (advices 6) (advices 7)
        (advices 8)) fun add =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Mul.configure_preservesGateSelectorsAllocated
        add rangeCheck advices) fun mul =>
    Configure.PreservesGateSelectorsAllocated.bind
      (MulFixed.configure_preservesGateSelectorsAllocated
        lagrangeCoeffs (advices 4) (advices 5)
        add addIncomplete) fun mulFixed =>
    Configure.PreservesGateSelectorsAllocated.bind
      (MulFixed.FullWidth.configure_preservesGateSelectorsAllocated
        mulFixed) fun mulFixedFull =>
    Configure.PreservesGateSelectorsAllocated.bind
      (MulFixed.Short.configure_preservesGateSelectorsAllocated
        mulFixed) fun mulFixedShort =>
    Configure.PreservesGateSelectorsAllocated.bind
      (MulFixed.BaseFieldElem.configure_preservesGateSelectorsAllocated
        ![advices 6, advices 7, advices 8]
        rangeCheck mulFixed) fun mulFixedBaseField =>
    Configure.PreservesGateSelectorsAllocated.pure
      ({ witnessPoint, addIncomplete, add, mul,
         mulFixedFull, mulFixedShort,
         mulFixedBaseField } : EccConfig)

end Ecc

namespace Action.Circuit

@[circuit_norm]
theorem orchardGate_selectorsOwned
    (qOrchard : Selector) (advices : Fin 10 → Column .advice) :
    (orchardGate qOrchard advices).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

/--
The Action configure program allocates every selector referenced by one of its
registered gates.  The proof follows the configure call graph; it does not unfold
the completed constraint system.
-/
theorem configure_preservesGateSelectorsAllocated
    (G : Specs.Sinsemilla.Generators) :
    Configure.PreservesGateSelectorsAllocated (configure G) := by
  unfold configure
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a0
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a1
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a2
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a3
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a4
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a5
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a6
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a7
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a8
  apply Configure.PreservesGateSelectorsAllocated.bind
    Configure.PreservesGateSelectorsAllocated.adviceColumn
  intro a9
  let advices : Fin 10 → Column .advice :=
    ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  apply Configure.PreservesGateSelectorsAllocated.selectorCreateGateThen
    (fun qOrchard => orchardGate qOrchard advices)
    (fun _ => rfl)
    (fun qOrchard =>
      orchardGate_selectorsOwned qOrchard advices)
  intro qOrchard
  exact Configure.PreservesGateSelectorsAllocated.bind
      (AddChip.configure_preservesGateSelectorsAllocated a7 a8 a6)
        fun addChipConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.lookupTableColumn fun tableIdx =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.lookupTableColumn fun tableX =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.lookupTableColumn fun tableY =>
    let genTable : Sinsemilla.GeneratorTableConfig :=
      { tableIdx, tableX, tableY }
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.instanceColumn fun primary =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        primary.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a0.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a2.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a3.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a4.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a5.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a6.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a7.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a8.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality a9.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l0 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l1 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l2 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l3 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l4 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l5 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l6 =>
    Configure.PreservesGateSelectorsAllocated.bind
      Configure.PreservesGateSelectorsAllocated.fixedColumn fun l7 =>
    let lagrangeCoeffs : Fin 8 → Column .fixed :=
      ![l0, l1, l2, l3, l4, l5, l6, l7]
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableConstant l0) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (LookupRangeCheck.configure_preservesGateSelectorsAllocated
        10 a9 tableIdx) fun lookupConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.configure_preservesGateSelectorsAllocated
        advices lagrangeCoeffs lookupConfig) fun eccConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Poseidon.configure_preservesGateSelectorsAllocated
        ![a6, a7, a8] a5 ![l2, l3, l4] ![l5, l6, l7])
        fun poseidonConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Sinsemilla.HashPiece.configure_preservesGateSelectorsAllocated
        G a0 a1 a2 a3 a4 a6 l0 genTable) fun sinsemilla1 =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Sinsemilla.Merkle.configure_preservesGateSelectorsAllocated
        sinsemilla1) fun merkle1 =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Sinsemilla.HashPiece.configure_preservesGateSelectorsAllocated
        G a5 a6 a7 a8 a9 a7 l1 genTable) fun sinsemilla2 =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Sinsemilla.Merkle.configure_preservesGateSelectorsAllocated
        sinsemilla2) fun merkle2 =>
    Configure.PreservesGateSelectorsAllocated.bind
      (CommitIvk.configure_preservesGateSelectorsAllocated advices)
        fun commitIvkConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (NoteCommit.configure_preservesGateSelectorsAllocated advices)
        fun noteCommitOld =>
    Configure.PreservesGateSelectorsAllocated.bind
      (NoteCommit.configure_preservesGateSelectorsAllocated advices)
        fun noteCommitNew =>
    Configure.PreservesGateSelectorsAllocated.pure
      ({ primary, qOrchard, advices, addChipConfig, eccConfig,
         poseidonConfig, sinsemilla1, merkle1, sinsemilla2, merkle2,
         commitIvkConfig, noteCommitOld, noteCommitNew,
         lookupConfig } : Config)

end Action.Circuit

end Zcash.Circuits

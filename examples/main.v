From CFGKAT.Semantics Require Export AutomataResolution.
From CFGKAT.Semantics Require Export ExpressionSemantics.
From CFGKAT.Semantics Require Export SyntacticAutomata.
From CFGKAT.Soundness Require Export Soundness.
From CFGKAT.Completeness Require Export BooleanAlgebraCompleteness.
From CFGKAT.Completeness Require Export Completeness.
From CFGKAT.Examples Require Export ShortCircuitTransform.
From CFGKAT.Examples Require Export ErosaHendrenLoopCase.

Print CFGKATBooleanAlgebraEquivalent.

Check BooleanAlgebra_sound.
Check Boolean_denotation_completeness.

Print CFGKATExpressionFiniteDynamics.
Print CFGKATExpressionDynamics.

Print ResolveCFGKATAutomatonFiniteDynamics.
Print ResolveCFGKATAutomatonDynamics.

Print CFGKATEquiv.

Check CFGKATEquiv_sound.
Check completeness.

Check short_circuit_transform.

Print eh_source_program.
Print eh_transformed_loop_body.
Print eh_transformed_program.
Check erosa_hendren_loop_case.

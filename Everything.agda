module Everything where

-- Definitions and properties of the raw syntax of untyped pre-terms.
-- Both the "implicit" and the "explicit" formulations rely on these
-- modules for their pre-syntax.
import Syntax.Raw

-- Definition of the raw syntax of pre-terms given in locally-nameless
-- style.
import Syntax.Raw.Term

-- Definitions and properties of contexts.
import Syntax.Raw.Context

-- Decidable syntactic equality between pre-terms.
import Syntax.Raw.Equality

-- Definitions and properties of untyped evaluation of pre-terms
-- according to weak lambda-reduction.
import Syntax.Raw.Evaluation

-- The actual definition of evaluation.
import Syntax.Raw.Evaluation.Evaluation

-- Definition and properties of normal forms under weak
-- lambda-reduction.
import Syntax.Raw.Evaluation.NormalForm

-- Properties of evaluation
import Syntax.Raw.Evaluation.Properties

-- Lemmas about the interaction between evaluation and substitution.
import Syntax.Raw.Evaluation.SubSwap

-- Definitions and properties of substitution over free De Bruijn
-- levels.
import Syntax.Raw.MetaSubstitution

-- Definitions and properties of renamings (weakenings) over De Bruijn
-- indices.
import Syntax.Raw.Renaming

-- Definitions and properties of substitutions over De Bruijn indices.
import Syntax.Raw.Substitution

-- Definitions and properties of typing judgments.
-- Both the "implicit" and the "explicit" formulations rely on these
-- modules for typing judgments (unlike judgmental equality).
import Syntax.Typed

-- The "implicit" (or standard) formulation of weak lambda-calculus.
import Implicit

-- The "explicit" weak lambda-calculus.
import Explicit

-- Definitions and properties of judgmental equality of the "explicit"
-- calculus.
import Explicit.Equality

-- Semantics of the explicit calculus.
import Explicit.Semantics

-- Semantic domain
import Explicit.Semantics.Domain

-- Completeness of NbE 
import Explicit.Semantics.Completeness

-- Definitions and properties of semantic types.
import Explicit.Semantics.Completeness.SemanticType

-- Proof of completeness of NbE, and definition of the total and
-- computable normalization function for well-typed terms.
import Explicit.Semantics.Completeness.Theorem

-- Soundness of NbE
import Explicit.Semantics.Soundness

-- Definitions and properties of Kripke logical relations.
import Explicit.Semantics.Soundness.LogicalRelation

-- Proof of soundness of NbE
import Explicit.Semantics.Soundness.Theorem

-- The proof of equivalence between the "implicit" and the "explicit"
-- formulations.
import Correspondence

-- Proof of normalization for both calculi.
import Normalization

-- Proof of decidability of judgmental equality for both calculi.
import Decide


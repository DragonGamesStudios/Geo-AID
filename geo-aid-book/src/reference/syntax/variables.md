# Variables

> <sup>**Syntax**</sup>\
> *LetStatement* :\
> &nbsp;&nbsp; `let` *VariableDefinition* (`,` *VariableDefinition*)<sup>\*</sup> `=` *[Expression&lt;true&gt;](expressions.md)* (*[RuleOp](rules.md)* *[Expression&lt;true&gt;](expressions.md)*)<sup>?</sup> `;`\
> \
> *VariableDefinition* :\
> &nbsp;&nbsp; [IDENT](identifiers.md) *[Properties](properties.md)*<sup>?</sup>

A let statement creates variables given on the left hand side. The lhs of the statement can contain multiple variables. In that, case if the rhs has no iteration, all variables will be set to the given definition (no the same value, though). If there is one level of iteration, all variables will get their respective definition. More levels of iteration are not allowed.

The rhs expression of the statement can either become the variable's definition or it can be unpacked onto a point collection. Point collection variables are invalid. A point collection may be used on the right hand side only if the identifier on the left is a point collection.

After each variable name there can be given properties that are later applied to the defining expression(s).

The let statement also accepts a single rule after its right hand side. It behaves as if the lhs was a sequence of variable accesses in a 0-id iterator.
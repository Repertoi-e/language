# PEG grammar for Python

@trailer '''
void *
_PyPegen_parse(Parser *p)
{
    // Initialize keywords
    p->keywords = reserved_keywords;
    p->n_keyword_lists = n_keyword_lists;
    p->soft_keywords = soft_keywords;

    // Run parser
    void *result = NULL;
    if (p->start_rule == Py_file_input) {
        result = file_rule(p);
    } else if (p->start_rule == Py_single_input) {
        result = interactive_rule(p);
    } else if (p->start_rule == Py_eval_input) {
        result = eval_rule(p);
    } else if (p->start_rule == Py_func_type_input) {
        result = func_type_rule(p);
    }

    return result;
}
'''

# ========================= START OF THE GRAMMAR =========================

# General grammatical elements and rules:
#
# * Strings with double quotes (") denote SOFT KEYWORDS
# * Strings with single quotes (') denote KEYWORDS
# * Upper case names (NAME) denote tokens in the Grammar/Tokens file
# * Rule names starting with "invalid_" are used for specialized syntax errors
#     - These rules are NOT used in the first pass of the parser.
#     - Only if the first pass fails to parse, a second pass including the invalid
#       rules will be executed.
#     - If the parser fails in the second phase with a generic syntax error, the
#       location of the generic failure of the first pass will be used (this avoids
#       reporting incorrect locations due to the invalid rules).
#     - The order of the alternatives involving invalid rules matter
#       (like any rule in PEG).
#
# Grammar Syntax (see PEP 617 for more information):
#
# rule_name: expression
#   Optionally, a type can be included right after the rule name, which
#   specifies the return type of the C or Python function corresponding to the
#   rule:
# rule_name[return_type]: expression
#   If the return type is omitted, then a void * is returned in C and an Any in
#   Python.
# e1 e2
#   Match e1, then match e2.
# e1 | e2
#   Match e1 or e2.
#   The first alternative can also appear on the line after the rule name for
#   formatting purposes. In that case, a | must be used before the first
#   alternative, like so:
#       rule_name[return_type]:
#            | first_alt
#            | second_alt
# ( e )
#   Match e (allows also to use other operators in the group like '(e)*')
# [ e ] or e?
#   Optionally match e.
# e*
#   Match zero or more occurrences of e.
# e+
#   Match one or more occurrences of e.
# s.e+
#   Match one or more occurrences of e, separated by s. The generated parse tree
#   does not include the separator. This is otherwise identical to (e (s e)*).
# &e
#   Succeed if e can be parsed, without consuming any input.
# !e
#   Fail if e can be parsed, without consuming any input.
# ~
#   Commit to the current alternative, even if it fails to parse.
# &&e
#   Eager parse e. The parser will not backtrack and will immediately 
#   fail with SyntaxError if e cannot be parsed.
#

# STARTING RULES
# ==============

file[mod_ty]: a=[statements] ENDMARKER { _PyPegen_make_module(p, a) }
interactive[mod_ty]: a=statement_newline { _PyAST_Interactive(a, p->arena) }
eval[mod_ty]: a=expressions NEWLINE* ENDMARKER { _PyAST_Expression(a, p->arena) }
func_type[mod_ty]: '(' a=[type_expressions] ')' '->' b=expression NEWLINE* ENDMARKER { _PyAST_FunctionType(a, b, p->arena) }

# GENERAL STATEMENTS
# ==================

statements[asdl_stmt_seq*]: a=statement+ { (asdl_stmt_seq*)_PyPegen_seq_flatten(p, a) }

statement[asdl_stmt_seq*]: a=compound_stmt { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) } | a[asdl_stmt_seq*]=simple_stmts { a }

statement_newline[asdl_stmt_seq*]:
    | a=compound_stmt NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) }
    | simple_stmts
    | NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, CHECK(stmt_ty, _PyAST_Pass(EXTRA))) }
    | ENDMARKER { _PyPegen_interactive_exit(p) }

simple_stmts[asdl_stmt_seq*]:
    | a=simple_stmt !';' NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) } # Not needed, there for speedup
    | a[asdl_stmt_seq*]=';'.simple_stmt+ [';'] NEWLINE { a }

# NOTE: assignment MUST precede expression, else parsing a simple assignment
# will throw a SyntaxError.
simple_stmt[stmt_ty] (memo):
    | assignment
    | &"type" type_alias
    | e=star_expressions { _PyAST_Expr(e, EXTRA) }
    | &'return' return_stmt
    | &('import' | 'from') import_stmt
    | &'raise' raise_stmt
    | 'pass' { _PyAST_Pass(EXTRA) }
    | &'del' del_stmt
    | &'yield' yield_stmt
    | &'assert' assert_stmt
    | 'break' { _PyAST_Break(EXTRA) }
    | 'continue' { _PyAST_Continue(EXTRA) }
    | &'global' global_stmt
    | &'nonlocal' nonlocal_stmt

compound_stmt[stmt_ty]:
    | &('def' | '@' | 'async') function_def
    | &'if' if_stmt
    | &('class' | '@') class_def
    | &('with' | 'async') with_stmt
    | &('for' | 'async') for_stmt
    | &'try' try_stmt
    | &'while' while_stmt
    | match_stmt

# SIMPLE STATEMENTS
# =================

# NOTE: annotated_rhs may start with 'yield'; yield_expr must start with 'yield'
assignment[stmt_ty]:
    | a=NAME ':' b=expression c=['=' d=annotated_rhs { d }] {
        CHECK_VERSION(
            stmt_ty,
            6,
            "Variable annotation syntax is",
            _PyAST_AnnAssign(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), b, c, 1, EXTRA)
        ) }
    | a=('(' b=single_target ')' { b }
         | single_subscript_attribute_target) ':' b=expression c=['=' d=annotated_rhs { d }] {
        CHECK_VERSION(stmt_ty, 6, "Variable annotations syntax is", _PyAST_AnnAssign(a, b, c, 0, EXTRA)) }
    | a[asdl_expr_seq*]=(z=star_targets '=' { z })+ b=(yield_expr | star_expressions) !'=' tc=[TYPE_COMMENT] {
         _PyAST_Assign(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | a=single_target b=augassign ~ c=(yield_expr | star_expressions) {
         _PyAST_AugAssign(a, b->kind, c, EXTRA) }
    | invalid_assignment

annotated_rhs[expr_ty]: yield_expr | star_expressions

augassign[AugOperator*]:
    | '+=' { _PyPegen_augoperator(p, Add) }
    | '-=' { _PyPegen_augoperator(p, Sub) }
    | '*=' { _PyPegen_augoperator(p, Mult) }
    | '@=' { CHECK_VERSION(AugOperator*, 5, "The '@' operator is", _PyPegen_augoperator(p, MatMult)) }
    | '/=' { _PyPegen_augoperator(p, Div) }
    | '%=' { _PyPegen_augoperator(p, Mod) }
    | '&=' { _PyPegen_augoperator(p, BitAnd) }
    | '|=' { _PyPegen_augoperator(p, BitOr) }
    | '^=' { _PyPegen_augoperator(p, BitXor) }
    | '<<=' { _PyPegen_augoperator(p, LShift) }
    | '>>=' { _PyPegen_augoperator(p, RShift) }
    | '**=' { _PyPegen_augoperator(p, Pow) }
    | '//=' { _PyPegen_augoperator(p, FloorDiv) }

return_stmt[stmt_ty]:
    | 'return' a=[star_expressions] { _PyAST_Return(a, EXTRA) }

raise_stmt[stmt_ty]:
    | 'raise' a=expression b=['from' z=expression { z }] { _PyAST_Raise(a, b, EXTRA) }
    | 'raise' { _PyAST_Raise(NULL, NULL, EXTRA) }

global_stmt[stmt_ty]: 'global' a[asdl_expr_seq*]=','.NAME+ {
    _PyAST_Global(CHECK(asdl_identifier_seq*, _PyPegen_map_names_to_ids(p, a)), EXTRA) }

nonlocal_stmt[stmt_ty]: 'nonlocal' a[asdl_expr_seq*]=','.NAME+ {
    _PyAST_Nonlocal(CHECK(asdl_identifier_seq*, _PyPegen_map_names_to_ids(p, a)), EXTRA) }

del_stmt[stmt_ty]:
    | 'del' a=del_targets &(';' | NEWLINE) { _PyAST_Delete(a, EXTRA) }
    | invalid_del_stmt

yield_stmt[stmt_ty]: y=yield_expr { _PyAST_Expr(y, EXTRA) }

assert_stmt[stmt_ty]: 'assert' a=expression b=[',' z=expression { z }] { _PyAST_Assert(a, b, EXTRA) }

import_stmt[stmt_ty]:
    | invalid_import
    | import_name
    | import_from

# Import statements
# -----------------

import_name[stmt_ty]: 'import' a=dotted_as_names { _PyAST_Import(a, EXTRA) }
# note below: the ('.' | '...') is necessary because '...' is tokenized as ELLIPSIS
import_from[stmt_ty]:
    | 'from' a=('.' | '...')* b=dotted_name 'import' c=import_from_targets {
        _PyAST_ImportFrom(b->v.Name.id, c, _PyPegen_seq_count_dots(a), EXTRA) }
    | 'from' a=('.' | '...')+ 'import' b=import_from_targets {
        _PyAST_ImportFrom(NULL, b, _PyPegen_seq_count_dots(a), EXTRA) }
import_from_targets[asdl_alias_seq*]:
    | '(' a=import_from_as_names [','] ')' { a }
    | import_from_as_names !','
    | '*' { (asdl_alias_seq*)_PyPegen_singleton_seq(p, CHECK(alias_ty, _PyPegen_alias_for_star(p, EXTRA))) }
    | invalid_import_from_targets
import_from_as_names[asdl_alias_seq*]:
    | a[asdl_alias_seq*]=','.import_from_as_name+ { a }
import_from_as_name[alias_ty]:
    | a=NAME b=['as' z=NAME { z }] { _PyAST_alias(a->v.Name.id,
                                               (b) ? ((expr_ty) b)->v.Name.id : NULL,
                                               EXTRA) }
dotted_as_names[asdl_alias_seq*]:
    | a[asdl_alias_seq*]=','.dotted_as_name+ { a }
dotted_as_name[alias_ty]:
    | a=dotted_name b=['as' z=NAME { z }] { _PyAST_alias(a->v.Name.id,
                                                      (b) ? ((expr_ty) b)->v.Name.id : NULL,
                                                      EXTRA) }
dotted_name[expr_ty]:
    | a=dotted_name '.' b=NAME { _PyPegen_join_names_with_dot(p, a, b) }
    | NAME

# COMPOUND STATEMENTS
# ===================

# Common elements
# ---------------

block[asdl_stmt_seq*] (memo):
    | NEWLINE INDENT a=statements DEDENT { a }
    | simple_stmts
    | invalid_block

decorators[asdl_expr_seq*]: a[asdl_expr_seq*]=('@' f=named_expression NEWLINE { f })+ { a }

# Class definitions
# -----------------

class_def[stmt_ty]:
    | a=decorators b=class_def_raw { _PyPegen_class_def_decorators(p, a, b) }
    | class_def_raw

class_def_raw[stmt_ty]:
    | invalid_class_def_raw
    | 'class' a=NAME t=[type_params] b=['(' z=[arguments] ')' { z }] ':' c=block {
        _PyAST_ClassDef(a->v.Name.id,
                     (b) ? ((expr_ty) b)->v.Call.args : NULL,
                     (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                     c, NULL, t, EXTRA) }

# Function definitions
# --------------------

function_def[stmt_ty]:
    | d=decorators f=function_def_raw { _PyPegen_function_def_decorators(p, d, f) }
    | function_def_raw

function_def_raw[stmt_ty]:
    | invalid_def_raw
    | 'def' n=NAME t=[type_params] '(' params=[params] ')' a=['->' z=expression { z }] ':' tc=[func_type_comment] b=block {
        _PyAST_FunctionDef(n->v.Name.id,
                        (params) ? params : CHECK(arguments_ty, _PyPegen_empty_arguments(p)),
                        b, NULL, a, NEW_TYPE_COMMENT(p, tc), t, EXTRA) }
    | 'async' 'def' n=NAME t=[type_params] '(' params=[params] ')' a=['->' z=expression { z }] ':' tc=[func_type_comment] b=block {
        CHECK_VERSION(
            stmt_ty,
            5,
            "Async functions are",
            _PyAST_AsyncFunctionDef(n->v.Name.id,
                            (params) ? params : CHECK(arguments_ty, _PyPegen_empty_arguments(p)),
                            b, NULL, a, NEW_TYPE_COMMENT(p, tc), t, EXTRA)
        ) }

# Function parameters
# -------------------

params[arguments_ty]:
    | invalid_parameters
    | parameters

parameters[arguments_ty]:
    | a=slash_no_default b[asdl_arg_seq*]=param_no_default* c=param_with_default* d=[star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, a, NULL, b, c, d)) }
    | a=slash_with_default b=param_with_default* c=[star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, NULL, a, NULL, b, c)) }
    | a[asdl_arg_seq*]=param_no_default+ b=param_with_default* c=[star_etc] {
        _PyPegen_make_arguments(p, NULL, NULL, a, b, c) }
    | a=param_with_default+ b=[star_etc] { _PyPegen_make_arguments(p, NULL, NULL, NULL, a, b)}
    | a=star_etc { _PyPegen_make_arguments(p, NULL, NULL, NULL, NULL, a) }

# Some duplication here because we can't write (',' | &')'),
# which is because we don't support empty alternatives (yet).

slash_no_default[asdl_arg_seq*]:
    | a[asdl_arg_seq*]=param_no_default+ '/' ',' { a }
    | a[asdl_arg_seq*]=param_no_default+ '/' &')' { a }
slash_with_default[SlashWithDefault*]:
    | a=param_no_default* b=param_with_default+ '/' ',' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }
    | a=param_no_default* b=param_with_default+ '/' &')' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }

star_etc[StarEtc*]:
    | invalid_star_etc
    | '*' a=param_no_default b=param_maybe_default* c=[kwds] {
        _PyPegen_star_etc(p, a, b, c) }
    | '*' a=param_no_default_star_annotation b=param_maybe_default* c=[kwds] {
        _PyPegen_star_etc(p, a, b, c) }
    | '*' ',' b=param_maybe_default+ c=[kwds] {
        _PyPegen_star_etc(p, NULL, b, c) }
    | a=kwds { _PyPegen_star_etc(p, NULL, NULL, a) }

kwds[arg_ty]:
    | invalid_kwds
    | '**' a=param_no_default { a }

# One parameter.  This *includes* a following comma and type comment.
#
# There are three styles:
# - No default
# - With default
# - Maybe with default
#
# There are two alternative forms of each, to deal with type comments:
# - Ends in a comma followed by an optional type comment
# - No comma, optional type comment, must be followed by close paren
# The latter form is for a final parameter without trailing comma.
#

param_no_default[arg_ty]:
    | a=param ',' tc=TYPE_COMMENT? { _PyPegen_add_type_comment_to_arg(p, a, tc) }
    | a=param tc=TYPE_COMMENT? &')' { _PyPegen_add_type_comment_to_arg(p, a, tc) }
param_no_default_star_annotation[arg_ty]:
    | a=param_star_annotation ',' tc=TYPE_COMMENT? { _PyPegen_add_type_comment_to_arg(p, a, tc) }
    | a=param_star_annotation tc=TYPE_COMMENT? &')' { _PyPegen_add_type_comment_to_arg(p, a, tc) }
param_with_default[NameDefaultPair*]:
    | a=param c=default ',' tc=TYPE_COMMENT? { _PyPegen_name_default_pair(p, a, c, tc) }
    | a=param c=default tc=TYPE_COMMENT? &')' { _PyPegen_name_default_pair(p, a, c, tc) }
param_maybe_default[NameDefaultPair*]:
    | a=param c=default? ',' tc=TYPE_COMMENT? { _PyPegen_name_default_pair(p, a, c, tc) }
    | a=param c=default? tc=TYPE_COMMENT? &')' { _PyPegen_name_default_pair(p, a, c, tc) }
param[arg_ty]: a=NAME b=annotation? { _PyAST_arg(a->v.Name.id, b, NULL, EXTRA) }
param_star_annotation[arg_ty]: a=NAME b=star_annotation { _PyAST_arg(a->v.Name.id, b, NULL, EXTRA) }
annotation[expr_ty]: ':' a=expression { a }
star_annotation[expr_ty]: ':' a=star_expression { a }
default[expr_ty]: '=' a=expression { a } | invalid_default

# If statement
# ------------

if_stmt[stmt_ty]:
    | invalid_if_stmt
    | 'if' a=named_expression ':' b=block c=elif_stmt {
        _PyAST_If(a, b, CHECK(asdl_stmt_seq*, _PyPegen_singleton_seq(p, c)), EXTRA) }
    | 'if' a=named_expression ':' b=block c=[else_block] { _PyAST_If(a, b, c, EXTRA) }
elif_stmt[stmt_ty]:
    | invalid_elif_stmt
    | 'elif' a=named_expression ':' b=block c=elif_stmt {
        _PyAST_If(a, b, CHECK(asdl_stmt_seq*, _PyPegen_singleton_seq(p, c)), EXTRA) }
    | 'elif' a=named_expression ':' b=block c=[else_block] { _PyAST_If(a, b, c, EXTRA) }
else_block[asdl_stmt_seq*]:
    | invalid_else_stmt
    | 'else' &&':' b=block { b }

# While statement
# ---------------

while_stmt[stmt_ty]:
    | invalid_while_stmt
    | 'while' a=named_expression ':' b=block c=[else_block] { _PyAST_While(a, b, c, EXTRA) }

# For statement
# -------------

for_stmt[stmt_ty]:
    | invalid_for_stmt
    | 'for' t=star_targets 'in' ~ ex=star_expressions ':' tc=[TYPE_COMMENT] b=block el=[else_block] {
        _PyAST_For(t, ex, b, el, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'async' 'for' t=star_targets 'in' ~ ex=star_expressions ':' tc=[TYPE_COMMENT] b=block el=[else_block] {
        CHECK_VERSION(stmt_ty, 5, "Async for loops are", _PyAST_AsyncFor(t, ex, b, el, NEW_TYPE_COMMENT(p, tc), EXTRA)) }
    | invalid_for_target

# With statement
# --------------

with_stmt[stmt_ty]:
    | invalid_with_stmt_indent
    | 'with' '(' a[asdl_withitem_seq*]=','.with_item+ ','? ')' ':' tc=[TYPE_COMMENT] b=block {
       _PyAST_With(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'with' a[asdl_withitem_seq*]=','.with_item+ ':' tc=[TYPE_COMMENT] b=block {
        _PyAST_With(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'async' 'with' '(' a[asdl_withitem_seq*]=','.with_item+ ','? ')' ':' b=block {
       CHECK_VERSION(stmt_ty, 5, "Async with statements are", _PyAST_AsyncWith(a, b, NULL, EXTRA)) }
    | 'async' 'with' a[asdl_withitem_seq*]=','.with_item+ ':' tc=[TYPE_COMMENT] b=block {
       CHECK_VERSION(stmt_ty, 5, "Async with statements are", _PyAST_AsyncWith(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA)) }
    | invalid_with_stmt

with_item[withitem_ty]:
    | e=expression 'as' t=star_target &(',' | ')' | ':') { _PyAST_withitem(e, t, p->arena) }
    | invalid_with_item
    | e=expression { _PyAST_withitem(e, NULL, p->arena) }

# Try statement
# -------------

try_stmt[stmt_ty]:
    | invalid_try_stmt
    | 'try' &&':' b=block f=finally_block { _PyAST_Try(b, NULL, NULL, f, EXTRA) }
    | 'try' &&':' b=block ex[asdl_excepthandler_seq*]=except_block+ el=[else_block] f=[finally_block] { _PyAST_Try(b, ex, el, f, EXTRA) }
    | 'try' &&':' b=block ex[asdl_excepthandler_seq*]=except_star_block+ el=[else_block] f=[finally_block] {
        CHECK_VERSION(stmt_ty, 11, "Exception groups are",
                      _PyAST_TryStar(b, ex, el, f, EXTRA)) }


# Except statement
# ----------------

except_block[excepthandler_ty]:
    | invalid_except_stmt_indent
    | 'except' e=expression t=['as' z=NAME { z }] ':' b=block {
        _PyAST_ExceptHandler(e, (t) ? ((expr_ty) t)->v.Name.id : NULL, b, EXTRA) }
    | 'except' ':' b=block { _PyAST_ExceptHandler(NULL, NULL, b, EXTRA) }
    | invalid_except_stmt
except_star_block[excepthandler_ty]:
    | invalid_except_star_stmt_indent
    | 'except' '*' e=expression t=['as' z=NAME { z }] ':' b=block {
        _PyAST_ExceptHandler(e, (t) ? ((expr_ty) t)->v.Name.id : NULL, b, EXTRA) }
    | invalid_except_star_stmt
finally_block[asdl_stmt_seq*]:
    | invalid_finally_stmt
    | 'finally' &&':' a=block { a }

# Match statement
# ---------------

match_stmt[stmt_ty]:
    | "match" subject=subject_expr ':' NEWLINE INDENT cases[asdl_match_case_seq*]=case_block+ DEDENT {
        CHECK_VERSION(stmt_ty, 10, "Pattern matching is", _PyAST_Match(subject, cases, EXTRA)) }
    | invalid_match_stmt

subject_expr[expr_ty]:
    | value=star_named_expression ',' values=star_named_expressions? {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, value, values)), Load, EXTRA) }
    | named_expression

case_block[match_case_ty]:
    | invalid_case_block
    | "case" pattern=patterns guard=guard? ':' body=block {
        _PyAST_match_case(pattern, guard, body, p->arena) }

guard[expr_ty]: 'if' guard=named_expression { guard }

patterns[pattern_ty]:
    | patterns[asdl_pattern_seq*]=open_sequence_pattern {
        _PyAST_MatchSequence(patterns, EXTRA) }
    | pattern

pattern[pattern_ty]:
    | as_pattern
    | or_pattern

as_pattern[pattern_ty]:
    | pattern=or_pattern 'as' target=pattern_capture_target {
        _PyAST_MatchAs(pattern, target->v.Name.id, EXTRA) }
    | invalid_as_pattern

or_pattern[pattern_ty]:
    | patterns[asdl_pattern_seq*]='|'.closed_pattern+ {
        asdl_seq_LEN(patterns) == 1 ? asdl_seq_GET(patterns, 0) : _PyAST_MatchOr(patterns, EXTRA) }

closed_pattern[pattern_ty] (memo):
    | literal_pattern
    | capture_pattern
    | wildcard_pattern
    | value_pattern
    | group_pattern
    | sequence_pattern
    | mapping_pattern
    | class_pattern

# Literal patterns are used for equality and identity constraints
literal_pattern[pattern_ty]:
    | value=signed_number !('+' | '-') { _PyAST_MatchValue(value, EXTRA) }
    | value=complex_number { _PyAST_MatchValue(value, EXTRA) }
    | value=strings { _PyAST_MatchValue(value, EXTRA) }
    | 'None' { _PyAST_MatchSingleton(Py_None, EXTRA) }
    | 'True' { _PyAST_MatchSingleton(Py_True, EXTRA) }
    | 'False' { _PyAST_MatchSingleton(Py_False, EXTRA) }

# Literal expressions are used to restrict permitted mapping pattern keys
literal_expr[expr_ty]:
    | signed_number !('+' | '-')
    | complex_number
    | strings
    | 'None' { _PyAST_Constant(Py_None, NULL, EXTRA) }
    | 'True' { _PyAST_Constant(Py_True, NULL, EXTRA) }
    | 'False' { _PyAST_Constant(Py_False, NULL, EXTRA) }

complex_number[expr_ty]:
    | real=signed_real_number '+' imag=imaginary_number {
        _PyAST_BinOp(real, Add, imag, EXTRA) }
    | real=signed_real_number '-' imag=imaginary_number  {
        _PyAST_BinOp(real, Sub, imag, EXTRA) }

signed_number[expr_ty]:
    | NUMBER
    | '-' number=NUMBER { _PyAST_UnaryOp(USub, number, EXTRA) }

signed_real_number[expr_ty]:
    | real_number
    | '-' real=real_number { _PyAST_UnaryOp(USub, real, EXTRA) }

real_number[expr_ty]:
    | real=NUMBER { _PyPegen_ensure_real(p, real) }

imaginary_number[expr_ty]:
    | imag=NUMBER { _PyPegen_ensure_imaginary(p, imag) }

capture_pattern[pattern_ty]:
    | target=pattern_capture_target { _PyAST_MatchAs(NULL, target->v.Name.id, EXTRA) }

pattern_capture_target[expr_ty]:
    | !"_" name=NAME !('.' | '(' | '=') {
        _PyPegen_set_expr_context(p, name, Store) }

wildcard_pattern[pattern_ty]:
    | "_" { _PyAST_MatchAs(NULL, NULL, EXTRA) }

value_pattern[pattern_ty]:
    | attr=attr !('.' | '(' | '=') { _PyAST_MatchValue(attr, EXTRA) }

attr[expr_ty]:
    | value=name_or_attr '.' attr=NAME {
        _PyAST_Attribute(value, attr->v.Name.id, Load, EXTRA) }

name_or_attr[expr_ty]:
    | attr
    | NAME

group_pattern[pattern_ty]:
    | '(' pattern=pattern ')' { pattern }

sequence_pattern[pattern_ty]:
    | '[' patterns=maybe_sequence_pattern? ']' { _PyAST_MatchSequence(patterns, EXTRA) }
    | '(' patterns=open_sequence_pattern? ')' { _PyAST_MatchSequence(patterns, EXTRA) }

open_sequence_pattern[asdl_seq*]:
    | pattern=maybe_star_pattern ',' patterns=maybe_sequence_pattern? {
        _PyPegen_seq_insert_in_front(p, pattern, patterns) }

maybe_sequence_pattern[asdl_seq*]:
    | patterns=','.maybe_star_pattern+ ','? { patterns }

maybe_star_pattern[pattern_ty]:
    | star_pattern
    | pattern

star_pattern[pattern_ty] (memo):
    | '*' target=pattern_capture_target {
        _PyAST_MatchStar(target->v.Name.id, EXTRA) }
    | '*' wildcard_pattern {
        _PyAST_MatchStar(NULL, EXTRA) }

mapping_pattern[pattern_ty]:
    | '{' '}' {
        _PyAST_MatchMapping(NULL, NULL, NULL, EXTRA) }
    | '{' rest=double_star_pattern ','? '}' {
        _PyAST_MatchMapping(NULL, NULL, rest->v.Name.id, EXTRA) }
    | '{' items=items_pattern ',' rest=double_star_pattern ','? '}' {
        _PyAST_MatchMapping(
            CHECK(asdl_expr_seq*, _PyPegen_get_pattern_keys(p, items)),
            CHECK(asdl_pattern_seq*, _PyPegen_get_patterns(p, items)),
            rest->v.Name.id,
            EXTRA) }
    | '{' items=items_pattern ','? '}' {
        _PyAST_MatchMapping(
            CHECK(asdl_expr_seq*, _PyPegen_get_pattern_keys(p, items)),
            CHECK(asdl_pattern_seq*, _PyPegen_get_patterns(p, items)),
            NULL,
            EXTRA) }

items_pattern[asdl_seq*]:
    | ','.key_value_pattern+

key_value_pattern[KeyPatternPair*]:
    | key=(literal_expr | attr) ':' pattern=pattern {
        _PyPegen_key_pattern_pair(p, key, pattern) }

double_star_pattern[expr_ty]:
    | '**' target=pattern_capture_target { target }

class_pattern[pattern_ty]:
    | cls=name_or_attr '(' ')' {
        _PyAST_MatchClass(cls, NULL, NULL, NULL, EXTRA) }
    | cls=name_or_attr '(' patterns=positional_patterns ','? ')' {
        _PyAST_MatchClass(cls, patterns, NULL, NULL, EXTRA) }
    | cls=name_or_attr '(' keywords=keyword_patterns ','? ')' {
        _PyAST_MatchClass(
            cls, NULL,
            CHECK(asdl_identifier_seq*, _PyPegen_map_names_to_ids(p,
                CHECK(asdl_expr_seq*, _PyPegen_get_pattern_keys(p, keywords)))),
            CHECK(asdl_pattern_seq*, _PyPegen_get_patterns(p, keywords)),
            EXTRA) }
    | cls=name_or_attr '(' patterns=positional_patterns ',' keywords=keyword_patterns ','? ')' {
        _PyAST_MatchClass(
            cls,
            patterns,
            CHECK(asdl_identifier_seq*, _PyPegen_map_names_to_ids(p,
                CHECK(asdl_expr_seq*, _PyPegen_get_pattern_keys(p, keywords)))),
            CHECK(asdl_pattern_seq*, _PyPegen_get_patterns(p, keywords)),
            EXTRA) }
    | invalid_class_pattern

positional_patterns[asdl_pattern_seq*]:
    | args[asdl_pattern_seq*]=','.pattern+ { args }

keyword_patterns[asdl_seq*]:
    | ','.keyword_pattern+

keyword_pattern[KeyPatternPair*]:
    | arg=NAME '=' value=pattern { _PyPegen_key_pattern_pair(p, arg, value) }

# Type statement
# ---------------

type_alias[stmt_ty]:
    | "type" n=NAME t=[type_params] '=' b=expression {
        CHECK_VERSION(stmt_ty, 12, "Type statement is",
        _PyAST_TypeAlias(CHECK(expr_ty, _PyPegen_set_expr_context(p, n, Store)), t, b, EXTRA)) }

# Type parameter declaration
# --------------------------

type_params[asdl_type_param_seq*]: 
    | invalid_type_params
    | '[' t=type_param_seq ']' {
        CHECK_VERSION(asdl_type_param_seq *, 12, "Type parameter lists are", t) }

type_param_seq[asdl_type_param_seq*]: a[asdl_type_param_seq*]=','.type_param+ [','] { a }

type_param[type_param_ty] (memo):
    | a=NAME b=[type_param_bound] c=[type_param_default] { _PyAST_TypeVar(a->v.Name.id, b, c, EXTRA) }
    | invalid_type_param
    | '*' a=NAME b=[type_param_starred_default] { _PyAST_TypeVarTuple(a->v.Name.id, b, EXTRA) }
    | '**' a=NAME b=[type_param_default] { _PyAST_ParamSpec(a->v.Name.id, b, EXTRA) }

type_param_bound[expr_ty]: ':' e=expression { e }
type_param_default[expr_ty]: '=' e=expression {
    CHECK_VERSION(expr_ty, 13, "Type parameter defaults are", e) }
type_param_starred_default[expr_ty]: '=' e=star_expression {
    CHECK_VERSION(expr_ty, 13, "Type parameter defaults are", e) }

# EXPRESSIONS
# -----------

expressions[expr_ty]:
    | a=expression b=(',' c=expression { c })+ [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Load, EXTRA) }
    | a=expression ',' { _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_singleton_seq(p, a)), Load, EXTRA) }
    | expression

expression[expr_ty] (memo):
    | invalid_expression
    | invalid_legacy_expression
    | a=disjunction 'if' b=disjunction 'else' c=expression { _PyAST_IfExp(b, a, c, EXTRA) }
    | disjunction
    | lambdef

yield_expr[expr_ty]:
    | 'yield' 'from' a=expression { _PyAST_YieldFrom(a, EXTRA) }
    | 'yield' a=[star_expressions] { _PyAST_Yield(a, EXTRA) }

star_expressions[expr_ty]:
    | a=star_expression b=(',' c=star_expression { c })+ [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Load, EXTRA) }
    | a=star_expression ',' { _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_singleton_seq(p, a)), Load, EXTRA) }
    | star_expression

star_expression[expr_ty] (memo):
    | '*' a=bitwise_or { _PyAST_Starred(a, Load, EXTRA) }
    | expression

star_named_expressions[asdl_expr_seq*]: a[asdl_expr_seq*]=','.star_named_expression+ [','] { a }

star_named_expression[expr_ty]:
    | '*' a=bitwise_or { _PyAST_Starred(a, Load, EXTRA) }
    | named_expression

assignment_expression[expr_ty]:
    | a=NAME ':=' ~ b=expression {
        CHECK_VERSION(expr_ty, 8, "Assignment expressions are",
        _PyAST_NamedExpr(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), b, EXTRA)) }

named_expression[expr_ty]:
    | assignment_expression
    | invalid_named_expression
    | expression !':='

disjunction[expr_ty] (memo):
    | a=conjunction b=('or' c=conjunction { c })+ { _PyAST_BoolOp(
        Or,
        CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)),
        EXTRA) }
    | conjunction

conjunction[expr_ty] (memo):
    | a=inversion b=('and' c=inversion { c })+ { _PyAST_BoolOp(
        And,
        CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)),
        EXTRA) }
    | inversion

inversion[expr_ty] (memo):
    | 'not' a=inversion { _PyAST_UnaryOp(Not, a, EXTRA) }
    | comparison

# Comparison operators
# --------------------

comparison[expr_ty]:
    | a=bitwise_or b=compare_op_bitwise_or_pair+ {
        _PyAST_Compare(
            a,
            CHECK(asdl_int_seq*, _PyPegen_get_cmpops(p, b)),
            CHECK(asdl_expr_seq*, _PyPegen_get_exprs(p, b)),
            EXTRA) }
    | bitwise_or

compare_op_bitwise_or_pair[CmpopExprPair*]:
    | eq_bitwise_or
    | noteq_bitwise_or
    | lte_bitwise_or
    | lt_bitwise_or
    | gte_bitwise_or
    | gt_bitwise_or
    | notin_bitwise_or
    | in_bitwise_or
    | isnot_bitwise_or
    | is_bitwise_or

eq_bitwise_or[CmpopExprPair*]: '==' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Eq, a) }
noteq_bitwise_or[CmpopExprPair*]:
    | (tok='!=' { _PyPegen_check_barry_as_flufl(p, tok) ? NULL : tok}) a=bitwise_or {_PyPegen_cmpop_expr_pair(p, NotEq, a) }
lte_bitwise_or[CmpopExprPair*]: '<=' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, LtE, a) }
lt_bitwise_or[CmpopExprPair*]: '<' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Lt, a) }
gte_bitwise_or[CmpopExprPair*]: '>=' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, GtE, a) }
gt_bitwise_or[CmpopExprPair*]: '>' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Gt, a) }
notin_bitwise_or[CmpopExprPair*]: 'not' 'in' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, NotIn, a) }
in_bitwise_or[CmpopExprPair*]: 'in' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, In, a) }
isnot_bitwise_or[CmpopExprPair*]: 'is' 'not' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, IsNot, a) }
is_bitwise_or[CmpopExprPair*]: 'is' a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Is, a) }

# Bitwise operators
# -----------------

bitwise_or[expr_ty]:
    | a=bitwise_or '|' b=bitwise_xor { _PyAST_BinOp(a, BitOr, b, EXTRA) }
    | bitwise_xor

bitwise_xor[expr_ty]:
    | a=bitwise_xor '^' b=bitwise_and { _PyAST_BinOp(a, BitXor, b, EXTRA) }
    | bitwise_and

bitwise_and[expr_ty]:
    | a=bitwise_and '&' b=shift_expr { _PyAST_BinOp(a, BitAnd, b, EXTRA) }
    | shift_expr

shift_expr[expr_ty]:
    | a=shift_expr '<<' b=sum { _PyAST_BinOp(a, LShift, b, EXTRA) }
    | a=shift_expr '>>' b=sum { _PyAST_BinOp(a, RShift, b, EXTRA) }
    | invalid_arithmetic
    | sum

# Arithmetic operators
# --------------------

sum[expr_ty]:
    | a=sum '+' b=term { _PyAST_BinOp(a, Add, b, EXTRA) }
    | a=sum '-' b=term { _PyAST_BinOp(a, Sub, b, EXTRA) }
    | term

term[expr_ty]:
    | a=term '*' b=factor { _PyAST_BinOp(a, Mult, b, EXTRA) }
    | a=term '/' b=factor { _PyAST_BinOp(a, Div, b, EXTRA) }
    | a=term '//' b=factor { _PyAST_BinOp(a, FloorDiv, b, EXTRA) }
    | a=term '%' b=factor { _PyAST_BinOp(a, Mod, b, EXTRA) }
    | a=term '@' b=factor { CHECK_VERSION(expr_ty, 5, "The '@' operator is", _PyAST_BinOp(a, MatMult, b, EXTRA)) }
    | invalid_factor
    | factor

factor[expr_ty] (memo):
    | '+' a=factor { _PyAST_UnaryOp(UAdd, a, EXTRA) }
    | '-' a=factor { _PyAST_UnaryOp(USub, a, EXTRA) }
    | '~' a=factor { _PyAST_UnaryOp(Invert, a, EXTRA) }
    | power

power[expr_ty]:
    | a=await_primary '**' b=factor { _PyAST_BinOp(a, Pow, b, EXTRA) }
    | await_primary

# Primary elements
# ----------------

# Primary elements are things like "obj.something.something", "obj[something]", "obj(something)", "obj" ...

await_primary[expr_ty] (memo):
    | 'await' a=primary { CHECK_VERSION(expr_ty, 5, "Await expressions are", _PyAST_Await(a, EXTRA)) }
    | primary

primary[expr_ty]:
    | a=primary '.' b=NAME { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=primary b=genexp { _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=primary '(' b=[arguments] ')' {
        _PyAST_Call(a,
                 (b) ? ((expr_ty) b)->v.Call.args : NULL,
                 (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                 EXTRA) }
    | a=primary '[' b=slices ']' { _PyAST_Subscript(a, b, Load, EXTRA) }
    | atom

slices[expr_ty]:
    | a=slice !',' { a }
    | a[asdl_expr_seq*]=','.(slice | starred_expression)+ [','] { _PyAST_Tuple(a, Load, EXTRA) }

slice[expr_ty]:
    | a=[expression] ':' b=[expression] c=[':' d=[expression] { d }] { _PyAST_Slice(a, b, c, EXTRA) }
    | a=named_expression { a }

atom[expr_ty]:
    | NAME
    | 'True' { _PyAST_Constant(Py_True, NULL, EXTRA) }
    | 'False' { _PyAST_Constant(Py_False, NULL, EXTRA) }
    | 'None' { _PyAST_Constant(Py_None, NULL, EXTRA) }
    | &(STRING|FSTRING_START) strings
    | NUMBER
    | &'(' (tuple | group | genexp)
    | &'[' (list | listcomp)
    | &'{' (dict | set | dictcomp | setcomp)
    | '...' { _PyAST_Constant(Py_Ellipsis, NULL, EXTRA) }

group[expr_ty]:
    | '(' a=(yield_expr | named_expression) ')' { a }
    | invalid_group

# Lambda functions
# ----------------

lambdef[expr_ty]:
    | 'lambda' a=[lambda_params] ':' b=expression {
        _PyAST_Lambda((a) ? a : CHECK(arguments_ty, _PyPegen_empty_arguments(p)), b, EXTRA) }

lambda_params[arguments_ty]:
    | invalid_lambda_parameters
    | lambda_parameters

# lambda_parameters etc. duplicates parameters but without annotations
# or type comments, and if there's no comma after a parameter, we expect
# a colon, not a close parenthesis.  (For more, see parameters above.)
#
lambda_parameters[arguments_ty]:
    | a=lambda_slash_no_default b[asdl_arg_seq*]=lambda_param_no_default* c=lambda_param_with_default* d=[lambda_star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, a, NULL, b, c, d)) }
    | a=lambda_slash_with_default b=lambda_param_with_default* c=[lambda_star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, NULL, a, NULL, b, c)) }
    | a[asdl_arg_seq*]=lambda_param_no_default+ b=lambda_param_with_default* c=[lambda_star_etc] {
        _PyPegen_make_arguments(p, NULL, NULL, a, b, c) }
    | a=lambda_param_with_default+ b=[lambda_star_etc] { _PyPegen_make_arguments(p, NULL, NULL, NULL, a, b)}
    | a=lambda_star_etc { _PyPegen_make_arguments(p, NULL, NULL, NULL, NULL, a) }

lambda_slash_no_default[asdl_arg_seq*]:
    | a[asdl_arg_seq*]=lambda_param_no_default+ '/' ',' { a }
    | a[asdl_arg_seq*]=lambda_param_no_default+ '/' &':' { a }

lambda_slash_with_default[SlashWithDefault*]:
    | a=lambda_param_no_default* b=lambda_param_with_default+ '/' ',' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }
    | a=lambda_param_no_default* b=lambda_param_with_default+ '/' &':' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }

lambda_star_etc[StarEtc*]:
    | invalid_lambda_star_etc
    | '*' a=lambda_param_no_default b=lambda_param_maybe_default* c=[lambda_kwds] {
        _PyPegen_star_etc(p, a, b, c) }
    | '*' ',' b=lambda_param_maybe_default+ c=[lambda_kwds] {
        _PyPegen_star_etc(p, NULL, b, c) }
    | a=lambda_kwds { _PyPegen_star_etc(p, NULL, NULL, a) }

lambda_kwds[arg_ty]:
    | invalid_lambda_kwds
    | '**' a=lambda_param_no_default { a }

lambda_param_no_default[arg_ty]:
    | a=lambda_param ',' { a }
    | a=lambda_param &':' { a }
lambda_param_with_default[NameDefaultPair*]:
    | a=lambda_param c=default ',' { _PyPegen_name_default_pair(p, a, c, NULL) }
    | a=lambda_param c=default &':' { _PyPegen_name_default_pair(p, a, c, NULL) }
lambda_param_maybe_default[NameDefaultPair*]:
    | a=lambda_param c=default? ',' { _PyPegen_name_default_pair(p, a, c, NULL) }
    | a=lambda_param c=default? &':' { _PyPegen_name_default_pair(p, a, c, NULL) }
lambda_param[arg_ty]: a=NAME { _PyAST_arg(a->v.Name.id, NULL, NULL, EXTRA) }

# LITERALS
# ========

fstring_middle[expr_ty]:
    | fstring_replacement_field
    | t=FSTRING_MIDDLE { _PyPegen_constant_from_token(p, t) }
fstring_replacement_field[expr_ty]:
    | '{' a=annotated_rhs debug_expr='='? conversion=[fstring_conversion] format=[fstring_full_format_spec] rbrace='}' {
        _PyPegen_formatted_value(p, a, debug_expr, conversion, format, rbrace, EXTRA) }
    | invalid_replacement_field
fstring_conversion[ResultTokenWithMetadata*]:
    | conv_token="!" conv=NAME { _PyPegen_check_fstring_conversion(p, conv_token, conv) }
fstring_full_format_spec[ResultTokenWithMetadata*]:
    | colon=':' spec=fstring_format_spec* { _PyPegen_setup_full_format_spec(p, colon, (asdl_expr_seq *) spec, EXTRA) }
fstring_format_spec[expr_ty]:
    | t=FSTRING_MIDDLE { _PyPegen_decoded_constant_from_token(p, t) }
    | fstring_replacement_field
fstring[expr_ty]:
    | a=FSTRING_START b=fstring_middle* c=FSTRING_END { _PyPegen_joined_str(p, a, (asdl_expr_seq*)b, c) }

string[expr_ty]: s[Token*]=STRING { _PyPegen_constant_from_string(p, s) }
strings[expr_ty] (memo): a[asdl_expr_seq*]=(fstring|string)+ { _PyPegen_concatenate_strings(p, a, EXTRA) }

list[expr_ty]:
    | '[' a=[star_named_expressions] ']' { _PyAST_List(a, Load, EXTRA) }

tuple[expr_ty]:
    | '(' a=[y=star_named_expression ',' z=[star_named_expressions] { _PyPegen_seq_insert_in_front(p, y, z) } ] ')' {
        _PyAST_Tuple(a, Load, EXTRA) }

set[expr_ty]: '{' a=star_named_expressions '}' { _PyAST_Set(a, EXTRA) }

# Dicts
# -----

dict[expr_ty]:
    | '{' a=[double_starred_kvpairs] '}' {
        _PyAST_Dict(
            CHECK(asdl_expr_seq*, _PyPegen_get_keys(p, a)),
            CHECK(asdl_expr_seq*, _PyPegen_get_values(p, a)),
            EXTRA) }
    | '{' invalid_double_starred_kvpairs '}'

double_starred_kvpairs[asdl_seq*]: a=','.double_starred_kvpair+ [','] { a }

double_starred_kvpair[KeyValuePair*]:
    | '**' a=bitwise_or { _PyPegen_key_value_pair(p, NULL, a) }
    | kvpair

kvpair[KeyValuePair*]: a=expression ':' b=expression { _PyPegen_key_value_pair(p, a, b) }

# Comprehensions & Generators
# ---------------------------

for_if_clauses[asdl_comprehension_seq*]:
    | a[asdl_comprehension_seq*]=for_if_clause+ { a }

for_if_clause[comprehension_ty]:
    | 'async' 'for' a=star_targets 'in' ~ b=disjunction c[asdl_expr_seq*]=('if' z=disjunction { z })* {
        CHECK_VERSION(comprehension_ty, 6, "Async comprehensions are", _PyAST_comprehension(a, b, c, 1, p->arena)) }
    | 'for' a=star_targets 'in' ~ b=disjunction c[asdl_expr_seq*]=('if' z=disjunction { z })* {
        _PyAST_comprehension(a, b, c, 0, p->arena) }
    | invalid_for_if_clause
    | invalid_for_target

listcomp[expr_ty]:
    | '[' a=named_expression b=for_if_clauses ']' { _PyAST_ListComp(a, b, EXTRA) }
    | invalid_comprehension

setcomp[expr_ty]:
    | '{' a=named_expression b=for_if_clauses '}' { _PyAST_SetComp(a, b, EXTRA) }
    | invalid_comprehension

genexp[expr_ty]:
    | '(' a=( assignment_expression | expression !':=') b=for_if_clauses ')' { _PyAST_GeneratorExp(a, b, EXTRA) }
    | invalid_comprehension

dictcomp[expr_ty]:
    | '{' a=kvpair b=for_if_clauses '}' { _PyAST_DictComp(a->key, a->value, b, EXTRA) }
    | invalid_dict_comprehension

# FUNCTION CALL ARGUMENTS
# =======================

arguments[expr_ty] (memo):
    | a=args [','] &')' { a }
    | invalid_arguments

args[expr_ty]:
    | a[asdl_expr_seq*]=','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ b=[',' k=kwargs {k}] {
        _PyPegen_collect_call_seqs(p, a, b, EXTRA) }
    | a=kwargs { _PyAST_Call(_PyPegen_dummy_name(p),
                          CHECK_NULL_ALLOWED(asdl_expr_seq*, _PyPegen_seq_extract_starred_exprs(p, a)),
                          CHECK_NULL_ALLOWED(asdl_keyword_seq*, _PyPegen_seq_delete_starred_exprs(p, a)),
                          EXTRA) }

kwargs[asdl_seq*]:
    | a=','.kwarg_or_starred+ ',' b=','.kwarg_or_double_starred+ { _PyPegen_join_sequences(p, a, b) }
    | ','.kwarg_or_starred+
    | ','.kwarg_or_double_starred+

starred_expression[expr_ty]:
    | invalid_starred_expression_unpacking
    | '*' a=expression { _PyAST_Starred(a, Load, EXTRA) }
    | invalid_starred_expression

kwarg_or_starred[KeywordOrStarred*]:
    | invalid_kwarg
    | a=NAME '=' b=expression {
        _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(a->v.Name.id, b, EXTRA)), 1) }
    | a=starred_expression { _PyPegen_keyword_or_starred(p, a, 0) }

kwarg_or_double_starred[KeywordOrStarred*]:
    | invalid_kwarg
    | a=NAME '=' b=expression {
        _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(a->v.Name.id, b, EXTRA)), 1) }
    | '**' a=expression { _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(NULL, a, EXTRA)), 1) }

# ASSIGNMENT TARGETS
# ==================

# Generic targets
# ---------------

# NOTE: star_targets may contain *bitwise_or, targets may not.
star_targets[expr_ty]:
    | a=star_target !',' { a }
    | a=star_target b=(',' c=star_target { c })* [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Store, EXTRA) }

star_targets_list_seq[asdl_expr_seq*]: a[asdl_expr_seq*]=','.star_target+ [','] { a }

star_targets_tuple_seq[asdl_expr_seq*]:
    | a=star_target b=(',' c=star_target { c })+ [','] { (asdl_expr_seq*) _PyPegen_seq_insert_in_front(p, a, b) }
    | a=star_target ',' { (asdl_expr_seq*) _PyPegen_singleton_seq(p, a) }

star_target[expr_ty] (memo):
    | '*' a=(!'*' star_target) {
        _PyAST_Starred(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), Store, EXTRA) }
    | target_with_star_atom

target_with_star_atom[expr_ty] (memo):
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }
    | star_atom

star_atom[expr_ty]:
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=target_with_star_atom ')' { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=[star_targets_tuple_seq] ')' { _PyAST_Tuple(a, Store, EXTRA) }
    | '[' a=[star_targets_list_seq] ']' { _PyAST_List(a, Store, EXTRA) }

single_target[expr_ty]:
    | single_subscript_attribute_target
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=single_target ')' { a }

single_subscript_attribute_target[expr_ty]:
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }

t_primary[expr_ty]:
    | a=t_primary '.' b=NAME &t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=t_primary '[' b=slices ']' &t_lookahead { _PyAST_Subscript(a, b, Load, EXTRA) }
    | a=t_primary b=genexp &t_lookahead {
        _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=t_primary '(' b=[arguments] ')' &t_lookahead {
        _PyAST_Call(a,
                 (b) ? ((expr_ty) b)->v.Call.args : NULL,
                 (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                 EXTRA) }
    | a=atom &t_lookahead { a }

t_lookahead: '(' | '[' | '.'

# Targets for del statements
# --------------------------

del_targets[asdl_expr_seq*]: a[asdl_expr_seq*]=','.del_target+ [','] { a }

del_target[expr_ty] (memo):
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Del, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Del, EXTRA) }
    | del_t_atom

del_t_atom[expr_ty]:
    | a=NAME { _PyPegen_set_expr_context(p, a, Del) }
    | '(' a=del_target ')' { _PyPegen_set_expr_context(p, a, Del) }
    | '(' a=[del_targets] ')' { _PyAST_Tuple(a, Del, EXTRA) }
    | '[' a=[del_targets] ']' { _PyAST_List(a, Del, EXTRA) }

# TYPING ELEMENTS
# ---------------

# type_expressions allow */** but ignore them
type_expressions[asdl_expr_seq*]:
    | a=','.expression+ ',' '*' b=expression ',' '**' c=expression {
        (asdl_expr_seq*)_PyPegen_seq_append_to_end(
            p,
            CHECK(asdl_seq*, _PyPegen_seq_append_to_end(p, a, b)),
            c) }
    | a=','.expression+ ',' '*' b=expression { (asdl_expr_seq*)_PyPegen_seq_append_to_end(p, a, b) }
    | a=','.expression+ ',' '**' b=expression { (asdl_expr_seq*)_PyPegen_seq_append_to_end(p, a, b) }
    | '*' a=expression ',' '**' b=expression {
        (asdl_expr_seq*)_PyPegen_seq_append_to_end(
            p,
            CHECK(asdl_seq*, _PyPegen_singleton_seq(p, a)),
            b) }
    | '*' a=expression { (asdl_expr_seq*)_PyPegen_singleton_seq(p, a) }
    | '**' a=expression { (asdl_expr_seq*)_PyPegen_singleton_seq(p, a) }
    | a[asdl_expr_seq*]=','.expression+ {a}

func_type_comment[Token*]:
    | NEWLINE t=TYPE_COMMENT &(NEWLINE INDENT) { t }  # Must be followed by indented block
    | invalid_double_type_comments
    | TYPE_COMMENT

# ========================= END OF THE GRAMMAR ===========================



# ========================= START OF INVALID RULES =======================

# From here on, there are rules for invalid syntax with specialised error messages
invalid_arguments:
    | ((','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ ',' kwargs) | kwargs) a=',' ','.(starred_expression !'=')+ {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "iterable argument unpacking follows keyword argument unpacking") }
    | a=expression b=for_if_clauses ',' [args | expression for_if_clauses] {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
    | a=NAME b='=' expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
    | (args ',')? a=NAME b='=' &(',' | ')') {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected argument value expression")}
    | a=args b=for_if_clauses { _PyPegen_nonparen_genexp_in_call(p, a, b) }
    | args ',' a=expression b=for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
    | a=args ',' args { _PyPegen_arguments_parsing_error(p, a) }
invalid_kwarg:
    | a[Token*]=('True'|'False'|'None') b='=' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to %s", PyBytes_AS_STRING(a->bytes)) }
    | a=NAME b='=' expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
    | !(NAME '=') a=expression b='=' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b, "expression cannot contain assignment, perhaps you meant \"==\"?") }
    | a='**' expression '=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to keyword argument unpacking") }

# IMPORTANT: Note that the "_without_invalid" suffix causes the rule to not call invalid rules under it
expression_without_invalid[expr_ty]:
    | a=disjunction 'if' b=disjunction 'else' c=expression { _PyAST_IfExp(b, a, c, EXTRA) }
    | disjunction
    | lambdef
invalid_legacy_expression:
    | a=NAME !'(' b=star_expressions {
        _PyPegen_check_legacy_stmt(p, a) ? RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b,
            "Missing parentheses in call to '%U'. Did you mean %U(...)?", a->v.Name.id, a->v.Name.id) : NULL}

invalid_type_param:
    | '*' a=NAME colon=':' e=expression {
            RAISE_SYNTAX_ERROR_STARTING_FROM(colon, e->kind == Tuple_kind
                ? "cannot use constraints with TypeVarTuple"
                : "cannot use bound with TypeVarTuple")
        }
    | '**' a=NAME colon=':' e=expression {
            RAISE_SYNTAX_ERROR_STARTING_FROM(colon, e->kind == Tuple_kind
                ? "cannot use constraints with ParamSpec"
                : "cannot use bound with ParamSpec")
        }

invalid_expression:
    # !(NAME STRING) is not matched so we don't show this error with some invalid string prefixes like: kf"dsfsdf"
    # Soft keywords need to also be ignored because they can be parsed as NAME NAME
   | !(NAME STRING | SOFT_KEYWORD) a=disjunction b=expression_without_invalid {
        _PyPegen_check_legacy_stmt(p, a) ? NULL : p->tokens[p->mark-1]->level == 0 ? NULL :
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Perhaps you forgot a comma?") }
   | a=disjunction 'if' b=disjunction !('else'|':') { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected 'else' after 'if' expression") }
   | a='lambda' [lambda_params] b=':' &FSTRING_MIDDLE  {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "f-string: lambda expressions are not allowed without parentheses") }

invalid_named_expression(memo):
    | a=expression ':=' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use assignment expressions with %s", _PyPegen_get_expr_name(a)) }
    | a=NAME '=' b=bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?") }
    | !(list|tuple|genexp|'True'|'None'|'False') a=bitwise_or b='=' bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot assign to %s here. Maybe you meant '==' instead of '='?",
                                          _PyPegen_get_expr_name(a)) }

invalid_assignment:
    | a=invalid_ann_assign_target ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a,
            "only single target (not %s) can be annotated",
            _PyPegen_get_expr_name(a)
        )}
    | a=star_named_expression ',' star_named_expressions* ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "only single target (not tuple) can be annotated") }
    | a=expression ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "illegal target for annotation") }
    | (star_targets '=')* a=star_expressions '=' {
        RAISE_SYNTAX_ERROR_INVALID_TARGET(STAR_TARGETS, a) }
    | (star_targets '=')* a=yield_expr '=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "assignment to yield expression not possible") }
    | a=star_expressions augassign annotated_rhs {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a,
            "'%s' is an illegal expression for augmented assignment",
            _PyPegen_get_expr_name(a)
        )}
invalid_ann_assign_target[expr_ty]:
    | list
    | tuple
    | '(' a=invalid_ann_assign_target ')' { a }
invalid_del_stmt:
    | 'del' a=star_expressions {
        RAISE_SYNTAX_ERROR_INVALID_TARGET(DEL_TARGETS, a) }
invalid_block:
    | NEWLINE !INDENT { RAISE_INDENTATION_ERROR("expected an indented block") }
invalid_comprehension:
    | ('[' | '(' | '{') a=starred_expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "iterable unpacking cannot be used in comprehension") }
    | ('[' | '{') a=star_named_expression ',' b=star_named_expressions for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, PyPegen_last_item(b, expr_ty),
        "did you forget parentheses around the comprehension target?") }
    | ('[' | '{') a=star_named_expression b=',' for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "did you forget parentheses around the comprehension target?") }
invalid_dict_comprehension:
    | '{' a='**' bitwise_or for_if_clauses '}' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "dict unpacking cannot be used in dict comprehension") }
invalid_parameters:
    | a="/" ',' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "at least one argument must precede /") }
    | (slash_no_default | slash_with_default) param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ may appear only once") }
    | slash_no_default? param_no_default* invalid_parameters_helper a=param_no_default {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "parameter without a default follows parameter with a default") }
    | param_no_default* a='(' param_no_default+ ','? b=')' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "Function parameters cannot be parenthesized") }
    | (slash_no_default | slash_with_default)? param_maybe_default* '*' (',' | param_no_default) param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ must be ahead of *") }
    | param_maybe_default+ '/' a='*' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expected comma between / and *") }
invalid_default:
    | a='=' &(')'|',') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expected default value expression") }
invalid_star_etc:
    | a='*' (')' | ',' (')' | '**')) { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "named arguments must follow bare *") }
    | '*' ',' TYPE_COMMENT { RAISE_SYNTAX_ERROR("bare * has associated type comment") }
    | '*' param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-positional argument cannot have default value") }
    | '*' (param_no_default | ',') param_maybe_default* a='*' (param_no_default | ',') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "* argument may appear only once") }
invalid_kwds:
    | '**' param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-keyword argument cannot have default value") }
    | '**' param ',' a=param { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "arguments cannot follow var-keyword argument") }
    | '**' param ',' a[Token*]=('*'|'**'|'/') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "arguments cannot follow var-keyword argument") }
invalid_parameters_helper: # This is only there to avoid type errors
    | a=slash_with_default { _PyPegen_singleton_seq(p, a) }
    | param_with_default+
invalid_lambda_parameters:
    | a="/" ',' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "at least one argument must precede /") }
    | (lambda_slash_no_default | lambda_slash_with_default) lambda_param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ may appear only once") }
    | lambda_slash_no_default? lambda_param_no_default* invalid_lambda_parameters_helper a=lambda_param_no_default {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "parameter without a default follows parameter with a default") }
    | lambda_param_no_default* a='(' ','.lambda_param+ ','? b=')' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "Lambda expression parameters cannot be parenthesized") }
    | (lambda_slash_no_default | lambda_slash_with_default)? lambda_param_maybe_default* '*' (',' | lambda_param_no_default) lambda_param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ must be ahead of *") }
    | lambda_param_maybe_default+ '/' a='*' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expected comma between / and *") }
invalid_lambda_parameters_helper:
    | a=lambda_slash_with_default { _PyPegen_singleton_seq(p, a) }
    | lambda_param_with_default+
invalid_lambda_star_etc:
    | '*' (':' | ',' (':' | '**')) { RAISE_SYNTAX_ERROR("named arguments must follow bare *") }
    | '*' lambda_param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-positional argument cannot have default value") }
    | '*' (lambda_param_no_default | ',') lambda_param_maybe_default* a='*' (lambda_param_no_default | ',') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "* argument may appear only once") }
invalid_lambda_kwds:
    | '**' lambda_param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-keyword argument cannot have default value") }
    | '**' lambda_param ',' a=lambda_param { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "arguments cannot follow var-keyword argument") }
    | '**' lambda_param ',' a[Token*]=('*'|'**'|'/') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "arguments cannot follow var-keyword argument") }
invalid_double_type_comments:
    | TYPE_COMMENT NEWLINE TYPE_COMMENT NEWLINE INDENT {
        RAISE_SYNTAX_ERROR("Cannot have two type comments on def") }
invalid_with_item:
    | expression 'as' a=expression &(',' | ')' | ':') {
        RAISE_SYNTAX_ERROR_INVALID_TARGET(STAR_TARGETS, a) }

invalid_for_if_clause:
    | 'async'? 'for' (bitwise_or (',' bitwise_or)* [',']) !'in' {
        RAISE_SYNTAX_ERROR("'in' expected after for-loop variables") }

invalid_for_target:
    | 'async'? 'for' a=star_expressions {
        RAISE_SYNTAX_ERROR_INVALID_TARGET(FOR_TARGETS, a) }

invalid_group:
    | '(' a=starred_expression ')' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use starred expression here") }
    | '(' a='**' expression ')' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use double starred expression here") }
invalid_import:
    | a='import' ','.dotted_name+ 'from' dotted_name {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "Did you mean to use 'from ... import ...' instead?") }
    | 'import' token=NEWLINE { 
        RAISE_SYNTAX_ERROR_STARTING_FROM(token, "Expected one or more names after 'import'") }

invalid_import_from_targets:
    | import_from_as_names ',' NEWLINE {
        RAISE_SYNTAX_ERROR("trailing comma not allowed without surrounding parentheses") }
    | token=NEWLINE { 
        RAISE_SYNTAX_ERROR_STARTING_FROM(token, "Expected one or more names after 'import'") }

invalid_with_stmt:
    | ['async'] 'with' ','.(expression ['as' star_target])+ NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | ['async'] 'with' '(' ','.(expressions ['as' star_target])+ ','? ')' NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
invalid_with_stmt_indent:
    | ['async'] a='with' ','.(expression ['as' star_target])+ ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'with' statement on line %d", a->lineno) }
    | ['async'] a='with' '(' ','.(expressions ['as' star_target])+ ','? ')' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'with' statement on line %d", a->lineno) }

invalid_try_stmt:
    | a='try' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'try' statement on line %d", a->lineno) }
    | 'try' ':' block !('except' | 'finally') { RAISE_SYNTAX_ERROR("expected 'except' or 'finally' block") }
    | 'try' ':' block* except_block+ a='except' b='*' expression ['as' NAME] ':' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot have both 'except' and 'except*' on the same 'try'") }
    | 'try' ':' block* except_star_block+ a='except' [expression ['as' NAME]] ':' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot have both 'except' and 'except*' on the same 'try'") }
invalid_except_stmt:
    | 'except' a=expression ',' expressions ['as' NAME ] ':' {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "multiple exception types must be parenthesized") }
    | a='except' expression ['as' NAME ] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='except' NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | 'except' expression 'as' a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use except statement with %s", _PyPegen_get_expr_name(a)) }
invalid_except_star_stmt:
    | 'except' '*' a=expression ',' expressions ['as' NAME ] ':' {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "multiple exception types must be parenthesized") }
    | a='except' '*' expression ['as' NAME ] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='except' '*' (NEWLINE | ':') { RAISE_SYNTAX_ERROR("expected one or more exception types") }
    | 'except' '*' expression 'as' a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use except* statement with %s", _PyPegen_get_expr_name(a)) }
invalid_finally_stmt:
    | a='finally' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'finally' statement on line %d", a->lineno) }
invalid_except_stmt_indent:
    | a='except' expression ['as' NAME ] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'except' statement on line %d", a->lineno) }
    | a='except' ':' NEWLINE !INDENT { RAISE_INDENTATION_ERROR("expected an indented block after 'except' statement on line %d", a->lineno) }
invalid_except_star_stmt_indent:
    | a='except' '*' expression ['as' NAME ] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'except*' statement on line %d", a->lineno) }
invalid_match_stmt:
    | "match" subject_expr NEWLINE { CHECK_VERSION(void*, 10, "Pattern matching is", RAISE_SYNTAX_ERROR("expected ':'") ) }
    | a="match" subject=subject_expr ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'match' statement on line %d", a->lineno) }
invalid_case_block:
    | "case" patterns guard? NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a="case" patterns guard? ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'case' statement on line %d", a->lineno) }
invalid_as_pattern:
    | or_pattern 'as' a="_" { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use '_' as a target") }
    | or_pattern 'as' a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use %s as pattern target", _PyPegen_get_expr_name(a)) }
invalid_class_pattern:
    | name_or_attr '(' a=invalid_class_argument_pattern  { RAISE_SYNTAX_ERROR_KNOWN_RANGE(
        PyPegen_first_item(a, pattern_ty),
        PyPegen_last_item(a, pattern_ty),
        "positional patterns follow keyword patterns") }
invalid_class_argument_pattern[asdl_pattern_seq*]:
    | [positional_patterns ','] keyword_patterns ',' a=positional_patterns { a }
invalid_if_stmt:
    | 'if' named_expression NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='if' a=named_expression ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'if' statement on line %d", a->lineno) }
invalid_elif_stmt:
    | 'elif' named_expression NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='elif' named_expression ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'elif' statement on line %d", a->lineno) }
invalid_else_stmt:
    | a='else' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'else' statement on line %d", a->lineno) }
invalid_while_stmt:
    | 'while' named_expression NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='while' named_expression ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'while' statement on line %d", a->lineno) }
invalid_for_stmt:
    | ['async'] 'for' star_targets 'in' star_expressions NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | ['async'] a='for' star_targets 'in' star_expressions ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'for' statement on line %d", a->lineno) }
invalid_def_raw:
    | ['async'] a='def' NAME [type_params] '(' [params] ')' ['->' expression] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after function definition on line %d", a->lineno) }
    | ['async'] 'def' NAME [type_params] &&'(' [params] ')' ['->' expression] &&':' [func_type_comment] block
invalid_class_def_raw:
    | 'class' NAME [type_params] ['(' [arguments] ')'] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='class' NAME [type_params] ['(' [arguments] ')'] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after class definition on line %d", a->lineno) }

invalid_double_starred_kvpairs:
    | ','.double_starred_kvpair+ ',' invalid_kvpair
    | expression ':' a='*' bitwise_or { RAISE_SYNTAX_ERROR_STARTING_FROM(a, "cannot use a starred expression in a dictionary value") }
    | expression a=':' &('}'|',') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expression expected after dictionary key and ':'") }
invalid_kvpair:
    | a=expression !(':') {
        RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, a->lineno, a->end_col_offset - 1, a->end_lineno, -1, "':' expected after dictionary key") }
    | expression ':' a='*' bitwise_or { RAISE_SYNTAX_ERROR_STARTING_FROM(a, "cannot use a starred expression in a dictionary value") }
    | expression a=':' &('}'|',') {RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expression expected after dictionary key and ':'") }
invalid_starred_expression_unpacking:
    | a='*' expression '=' b=expression { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to iterable argument unpacking") }
invalid_starred_expression:
    | '*' { RAISE_SYNTAX_ERROR("Invalid star expression") }

invalid_replacement_field:
    | '{' a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "f-string: valid expression required before '='") }
    | '{' a='!' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "f-string: valid expression required before '!'") }
    | '{' a=':' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "f-string: valid expression required before ':'") }
    | '{' a='}' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "f-string: valid expression required before '}'") }
    | '{' !annotated_rhs { RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting a valid expression after '{'")}
    | '{' annotated_rhs !('=' | '!' | ':' | '}') {
        PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting '=', or '!', or ':', or '}'") }
    | '{' annotated_rhs '=' !('!' | ':' | '}') {
        PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting '!', or ':', or '}'") }
    | '{' annotated_rhs '='? invalid_conversion_character
    | '{' annotated_rhs '='? ['!' NAME] !(':' | '}') {
        PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting ':' or '}'") }
    | '{' annotated_rhs '='? ['!' NAME] ':' fstring_format_spec* !'}' {
        PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting '}', or format specs") }
    | '{' annotated_rhs '='? ['!' NAME] !'}' {
        PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: expecting '}'") }

invalid_conversion_character:
    | '!' &(':' | '}') { RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: missing conversion character") }
    | '!' !NAME { RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: invalid conversion character") }

invalid_arithmetic:
    | sum ('+'|'-'|'*'|'/'|'%'|'//'|'@') a='not' b=inversion { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "'not' after an operator must be parenthesized") }
invalid_factor:
    | ('+' | '-' | '~') a='not' b=factor { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "'not' after an operator must be parenthesized") }

invalid_type_params:
    | '[' token=']' {
        RAISE_SYNTAX_ERROR_STARTING_FROM(
            token, 
            "Type parameter list cannot be empty")}
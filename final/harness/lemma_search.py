"""Release stub (probe/open_package/export_release.py): only _LEAN_KW, bound_names of the dev module, copied verbatim."""
import re
_LEAN_KW = {"theorem", "lemma", "fun", "by", "at", "with", "using", "only", "then", "else", "if", "match", "do", "let", "have", "show",
            "from", "exact", "apply", "intro", "intros", "obtain", "rcases", "rintro", "cases", "induction", "generalizing", "simp",
            "simp_all", "grind", "aesop", "omega", "rfl", "rw", "rwa", "erw", "refine", "use", "left", "right", "constructor",
            "case", "all_goals", "any_goals", "first", "next", "subst", "calc", "conv", "enter", "suffices", "this", "Type", "Prop",
            "Sort", "fun_prop", "norm_num", "linarith", "nlinarith", "positivity", "tauto", "ring", "field_simp", "congr", "ext",
            "funext", "specialize", "exists", "refine'", "split", "unfold", "dsimp", "simpa", "exfalso", "contradiction", "by_contra",
            "by_cases", "push_neg", "set", "change", "trivial", "assumption", "repeat", "try", "focus", "nofun", "nomatch",
            "classical", "decide", "rename_i", "exacts", "apply?", "exact?", "trace_state", "sorry", "open", "in", "where",
            "true", "false", "True", "False", "and", "or", "not", "fin_cases", "interval_cases", "gcongr", "bound", "infer_instance",
            "inferInstance", "Nat", "Int", "Real", "List", "Set", "Finset", "Option", "Bool", "Prod", "Fin", "ENat", "ENNReal", "NNReal"}

def bound_names(text: str) -> set[str]:
    """Names bound in the text: binders `(a b : T)`, `{a : T}`, `[inst : C]`, `∀ a b,`, `∃ x,`, `fun x =>`, goal-context lines
    `a b : T`, pattern binders `⟨a, b⟩`, `| succ n ih =>`, `intro a b`, `obtain ⟨…⟩`, `have h :`, `case X a b =>`."""
    out: set[str] = set()
    for grp in re.findall(r"[({⦃\[]\s*([^(){}\[\]:]+?)\s*:", text):
        out.update(x for x in grp.split() if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:∀|∃!?|fun|λ)\s+([^,:=(]+?)\s*(?:,|=>|:|↦)", text):
        out.update(x for x in re.split(r"[\s()⟨⟩]+", grp) if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for line in text.split("\n"):
        m = re.match(r"^\s*([^\W\d][\w'₀-₉]*(?:\s+[^\W\d][\w'₀-₉]*)*)\s*:\s", line)
        if m and not re.match(r"^\s*(theorem|lemma|have|show|def|case|example|instance)\b", line):
            out.update(m.group(1).split())
    for grp in re.findall(r"⟨([^⟨⟩]*)⟩", text):
        out.update(x for x in re.split(r"[\s,]+", grp) if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:\|\s*\w+|intro|intros|rintro|rename_i|case\s+\S+|next)\s+([^\n=:]*?)(?:=>|$)", text, re.M):
        out.update(x for x in grp.split() if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:have|obtain|set|let|generalize)\s+([^\W\d][\w'₀-₉]*)", text):
        out.add(grp)
    return {x for x in out if x not in _LEAN_KW or len(x) <= 2}


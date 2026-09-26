import os
import re

source_dir = "PMADLean"
files_to_scan = [f for f in os.listdir(source_dir) if f.endswith(".lean")]
#NOTE: DONT USE ANY IN `decl_pattern` IN COMMENTS IN
# Keep your exact pattern and blacklists completely untouched
decl_pattern = re.compile(r'\b(?:theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_\.]+)')
tactics_blacklist = {'have', 'rw', 'using', 'unfold', 'of', 'block'}

file_declarations = {}
decl_to_full_id = {}
def_nodes = set()          
node_complexity = {}       
cross_dependencies = {}
all_dependencies = {}      # Track internal + cross dependencies for complexity logic

# FIRST PASS: Extract declarations and pre-categorize trivial proofs based on file contents
for filename in files_to_scan:
    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)
    file_declarations[module] = []
    
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
        
        # Populate declarations
        for match in decl_pattern.finditer(content):
            name = match.group(1)
            if name not in tactics_blacklist:
                full_id = f"{module}_{name}"
                file_declarations[module].append((name, full_id))
                decl_to_full_id[name] = full_id
                
                # FIX: Look at the exact string match text directly to find definitions
                match_text = match.group(0)
                if any(match_text.startswith(kw) for kw in ['def', 'structure', 'inductive']):
                    def_nodes.add(full_id)

        # FIX: Check if blocks contain simple termination tokens *before* rendering loop runs
        blocks = re.split(r'\b(?:theorem|lemma|def|structure|inductive)\s+', content)
        for block in blocks[1:]:
            lines = block.strip().split("\n")
            if not lines or not lines[0]:
                continue
            # FIX: Target strictly the first string item index in the code lines array slice
            header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
            if not header_match:
                continue
            src_short = header_match.group(1)
            if src_short in tactics_blacklist:
                continue
            src_full = f"{module}_{src_short}"
            
            if src_full not in def_nodes:
                body_lower = block.lower()
                if 'rfl' in body_lower or 'le_refl' in body_lower:
                    node_complexity[src_full] = "trivial"
                else:
                    node_complexity[src_full] = "heavy"

# Establish visual grouping boxes to force readable vertical stacking
module_meta = {
    "Axioms": {"title": "Axioms.lean (Foundations)"},
    "Dynamics": {"title": "Dynamics.lean (Attractor Convergence)"},
    "Probability": {"title": "Probability.lean (Born Rule & Bounds)"},
    "Metrics": {"title": "Metrics.lean (Compliance Geometry)"},
    "Renormalization": {"title": "Renormalization.lean (Scale Decay)"},
    "Vorticity": {"title": "Vorticity.lean (Spacetime Synthesis)"},
    "Incompleteness": {"title": "Incompleteness.lean (Decoupled Limits)"},
    "Test": {"title": "Test.lean (spiral-vm runtime example)"},
    "PhyslibBridge": {"title": "PhyslibBridge.lean (Show equivalence with Physlib)"}
}

# Map edge connections cleanly
for filename in files_to_scan:
    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)
    if module not in module_meta:
        continue
        
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
        
    blocks = re.split(r'\b(?:theorem|lemma|def|structure|inductive)\s+', content)
    for block in blocks[1:]:
        lines = block.strip().split("\n")
        if not lines or not lines[0]:
            continue
        header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
        if not header_match:
            continue
            
        src_short = header_match.group(1)
        if src_short in tactics_blacklist:
            continue
        src_full = f"{module}_{src_short}"
        
        tokens = re.findall(r'\b([A-Za-z0-9_\.]+)\b', block)
        for token in tokens:
            if token in decl_to_full_id and token != src_short:
                tgt_full = decl_to_full_id[token]
                
                # Track for total dependency counts (Internal + Cross)
                if src_full not in all_dependencies:
                    all_dependencies[src_full] = set()
                all_dependencies[src_full].add(tgt_full)
                
                # Check for cross-module edge transformations
                is_cross = token not in [d[0] for d in file_declarations[module]]
                
                if is_cross:
                    tgt_module = tgt_full.split("_")[0]
                    if src_full not in cross_dependencies:
                        cross_dependencies[src_full] = []
                    cross_dependencies[src_full].append(f"{tgt_module}.{token}")

# Generate a high-scannability vertical layout output tree
md_lines = [
    "# 📐 Lean Project Architecture Map",
    "Below is the strict verification architecture layout compiled directly from source code dependencies.",
    "",
]

modules_order = ["Axioms", "Dynamics", "Probability", "Metrics", "Renormalization", "Vorticity", "Incompleteness", "Test", "PhyslibBridge"]
existing_modules = [m for m in modules_order if m in file_declarations and file_declarations[m]]

for idx, module in enumerate(existing_modules):
    meta = module_meta[module]
    decls = file_declarations[module]
    
    # Structural Visual Pipeline Header
    if idx > 0:
        md_lines.append("```text")
        md_lines.append("       │")
        md_lines.append("       ▼ [Cross-Module Dependency Pipeline]")
        md_lines.append("```")
        
    md_lines.append(f"### 📦 {meta['title']}")
    md_lines.append("<details open>")
    md_lines.append(f"<summary><b>View Module Elements ({len(decls)} items)</b></summary>")
    md_lines.append("")
    
    # Text-Based Visual Map Track inside the collapsible pane
    md_lines.append("```text")
    md_lines.append(f"┌─── [{module}.lean] ──────────────────────────────────────────────────┐")
    for short_name, full_id in decls:
        cross_deps = list(set(cross_dependencies.get(full_id, [])))
        total_dep_count = len(all_dependencies.get(full_id, set()))
        
        if full_id in def_nodes:
            tag = "[DEF]"
            icon = "⚙️"
        else:
            # FIX: Heavy if it relies on more than 0 total dependency and more than 0 cross deps
            complexity = "heavy" if (total_dep_count > 0 and len(cross_deps) > 0) else "trivial"
            tag = "[TRIV]" if complexity == "trivial" else "[CORE]"
            icon = "⬜" if complexity == "trivial" else "🔥"
            
        dep_track = f" ➔ Outbound to: {', '.join(cross_deps)}" if cross_deps else ""
        
        # Format a clean visual track row
        md_lines.append(f"│  ├─ {icon} {tag:<6} {short_name:<30} {dep_track}")
    md_lines.append(f"└──────────────────────────────────────────────────────────────────────┘")
    md_lines.append("```")
    md_lines.append("</details>")
    md_lines.append("")

with open("theorem_architecture.md", "w", encoding="utf-8") as out:
    out.write("\n".join(md_lines) + "\n")

print("✔ Optimized high-scannability dashboard written to theorem_architecture.md")

# ================================================================
# ADDITIVE HYPOTHESIS AUDIT
# ================================================================
#
# This section does NOT modify the existing architecture analysis.
#
# It builds a second, hypothesis-oriented view:
#
#   1. Extract theorem/lemma hypotheses from signatures
#   2. Detect direct textual use in the theorem body
#   3. Search the entire repository for references to each hypothesis
#   4. Classify with conservative heuristics (avoids false UNUSED)
#   5. Generate a hypothesis audit section
#
# IMPORTANT:
# This is source-level analysis, not elaborated Lean proof-term
# analysis. It therefore reports "textually used" rather than
# claiming semantic necessity.
# ================================================================

hypothesis_records = []
hypothesis_names = set()

# ------------------------------------------------
# Helpers
# ------------------------------------------------

def strip_comments(text):
    """
    Remove ordinary Lean line/block comments for the audit parser.
    This is deliberately separate from the existing parser so the
    original script remains untouched.
    """
    text = re.sub(r'/-.*?-/+', ' ', text, flags=re.S)
    text = re.sub(r'--.*$', ' ', text, flags=re.M)
    return text


def extract_decl_blocks(content):
    """
    Return approximate declaration blocks.

    This intentionally uses a separate parser from decl_pattern so
    the existing declaration logic remains unchanged.
    """
    pattern = re.compile(
        r'\b(theorem|lemma)\s+([A-Za-z0-9_\.]+)(.*?)(?=\n\s*(?:theorem|lemma|def|structure|inductive)\s+|\Z)',
        re.S
    )
    return pattern.finditer(content)


def extract_hypotheses(header):
    """
    Extract likely named hypotheses from a theorem/lemma signature.

    Handles common forms such as:

        (h : P)
        (h₁ : P)
        {h : P}
        [h : P]
        (h : ∀ x, ...)
        (h : A → B)

    This is deliberately conservative.
    """
    hypotheses = []

    binder_pattern = re.compile(
        r'[\(\{\[]\s*'
        r'([A-Za-z_][A-Za-z0-9_]*(?:\s+[A-Za-z_][A-Za-z0-9_]*)*)'
        r'\s*:\s*'
    )

    for match in binder_pattern.finditer(header):
        raw_names = match.group(1).strip()
        names = raw_names.split()

        for name in names:
            if name.startswith("h") or name.startswith("H"):
                hypotheses.append({
                    "name": name,
                    "type": None,
                    "binder_start": match.start(),
                    "binder_end": match.end()
                })

    return hypotheses


def extract_binder_types(header, hypotheses):
    """
    Recover an approximate type for each hypothesis by locating the
    next binder boundary.
    """
    for hyp in hypotheses:
        start = hyp["binder_end"]

        depth = 1
        i = start
        while i < len(header) and depth > 0:
            if header[i] in "({[":
                depth += 1
            elif header[i] in ")}]":
                depth -= 1
            i += 1

        type_text = header[start:i-1].strip()
        type_text = re.sub(r'\s+', ' ', type_text)
        hyp["type"] = type_text

    return hypotheses


def looks_definitional_identity(type_text):
    """
    Conservative heuristic for equality-shaped hypotheses that might
    be definitional. Does NOT prove rfl.
    """
    if not type_text:
        return False

    normalized = type_text.replace(" ", "")

    if "=" not in normalized:
        return False

    # Avoid inequalities
    if any(op in normalized for op in ["≤", "≥", "<", ">"]):
        return False

    return True


def classify_hypothesis(record, same_theorem_records):
    """
    Safer classification that reduces false UNUSED labels.

    Priority:
      1. Textual occurrence > 1          → USED
      2. Equality-shaped                 → DEFINITION_CANDIDATE
      3. Mentions other local hyps or
         looks like a bound/inequality   → POSSIBLY_USED
      4. Otherwise                       → UNUSED_CANDIDATE
    """
    name = record["hypothesis"]
    type_text = record["type"] or ""
    occurrences = 1 + sum(
        1 for _ in re.finditer(r'\b' + re.escape(name) + r'\b', record["block"])
    ) - 1   # binder itself counts as 1

    # Re-count properly
    pattern = re.compile(r'\b' + re.escape(name) + r'\b')
    occurrences = len(list(pattern.finditer(record["block"])))

    if occurrences > 1:
        return "USED"

    if looks_definitional_identity(type_text):
        return "DEFINITION_CANDIDATE"

    # Soft signal: type mentions other hypotheses of the same theorem
    other_names = {
        r["hypothesis"] for r in same_theorem_records
        if r["hypothesis"] != name
    }
    mentions_other = any(other in type_text for other in other_names)

    looks_like_bound = any(
        op in type_text for op in ["≤", "≥", "<", ">", "∈", "≠", "≤", "≥"]
    )

    if mentions_other or looks_like_bound:
        return "POSSIBLY_USED"

    return "UNUSED_CANDIDATE"
    
# ------------------------------------------------
# NEW PRE-PASS: Grab global variables at the top of the file
# ------------------------------------------------
with open(path, "r", encoding="utf-8") as f:
    raw_content = f.read()

content = strip_comments(raw_content)

# Detect if 'variable (ϕ : Trajectory N)' or similar exists globally in the file
global_variables = []
var_matches = re.findall(r'variable\s+\{?[^}]*\}?\s*\(([^:]+)\s*:\s*([^)]+)\)', content)
for name, vtype in var_matches:
    global_variables.append({"name": name.strip(), "type": vtype.strip()})

# ------------------------------------------------
# PASS A: collect theorem hypotheses (Updated)
# ------------------------------------------------
for match in extract_decl_blocks(content):
    theorem_name = match.group(2)
    block = match.group(0)

    # 1. Grab local hypotheses like before
    hypotheses = extract_hypotheses(block)
    hypotheses = extract_binder_types(block, hypotheses)
    
    # 2. INJECT GLOBAL VARIABLES DIRECTLY INTO THIS THEOREM'S RECORD
    # Only if the variable name actually appears inside this theorem text block!
    for g_var in global_variables:
        if re.search(r'\b' + re.escape(g_var["name"]) + r'\b', block):
            # If it's used in the body, Python acts like it was in the signature!
            hypotheses.append(g_var)



# ------------------------------------------------
# PASS A: collect theorem hypotheses
# ------------------------------------------------

for filename in files_to_scan:
    if not filename.endswith(".lean"):
        continue

    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)

    with open(path, "r", encoding="utf-8") as f:
        raw_content = f.read()

    content = strip_comments(raw_content)

    for match in extract_decl_blocks(content):
        kind = match.group(1)
        theorem_name = match.group(2)
        block = match.group(0)

        hypotheses = extract_hypotheses(block)
        hypotheses = extract_binder_types(block, hypotheses)

        if not hypotheses:
            continue

        for hyp in hypotheses:
            record = {
                "module": module,
                "theorem": theorem_name,
                "full_id": f"{module}_{theorem_name}",
                "hypothesis": hyp["name"],
                "type": hyp["type"],
                "block": block,
                "directly_used": False,
                "used_elsewhere": [],
                "classification": "UNKNOWN"
            }
            hypothesis_records.append(record)
            hypothesis_names.add(hyp["name"])


# ------------------------------------------------
# PASS B: direct use inside declaring theorem
# ------------------------------------------------

identifier_pattern_cache = {}

for record in hypothesis_records:
    hyp_name = record["hypothesis"]
    block = record["block"]

    if hyp_name not in identifier_pattern_cache:
        identifier_pattern_cache[hyp_name] = re.compile(
            r'\b' + re.escape(hyp_name) + r'\b'
        )

    occurrences = list(identifier_pattern_cache[hyp_name].finditer(block))
    record["directly_used"] = len(occurrences) > 1


# ------------------------------------------------
# PASS C: search for hypotheses elsewhere
# ------------------------------------------------

repo_files = {}

for filename in files_to_scan:
    path = os.path.join(source_dir, filename)
    with open(path, "r", encoding="utf-8") as f:
        repo_files[filename] = strip_comments(f.read())

for record in hypothesis_records:
    hyp_name = record["hypothesis"]
    declaring_file = record["module"] + ".lean"

    pattern = re.compile(r'\b' + re.escape(hyp_name) + r'\b')
    elsewhere = []

    for filename, content in repo_files.items():
        if filename == declaring_file:
            continue
        for match in pattern.finditer(content):
            line_number = content.count("\n", 0, match.start()) + 1
            elsewhere.append({"file": filename, "line": line_number})

    record["used_elsewhere"] = elsewhere


# ------------------------------------------------
# PASS D: classify (safer version)
# ------------------------------------------------

# Group records by theorem so we can see sibling hypotheses
from collections import defaultdict
by_theorem = defaultdict(list)
for r in hypothesis_records:
    by_theorem[(r["module"], r["theorem"])].append(r)

for record in hypothesis_records:
    siblings = by_theorem[(record["module"], record["theorem"])]
    record["classification"] = classify_hypothesis(record, siblings)


# ------------------------------------------------
# PASS E: upgrade classification when name appears elsewhere
# ------------------------------------------------

for record in hypothesis_records:
    if record["used_elsewhere"]:
        if record["classification"] in {"UNUSED_CANDIDATE", "POSSIBLY_USED"}:
            record["classification"] = "USED_ELSEWHERE"
        elif record["classification"] == "USED":
            record["classification"] = "USED_AND_REFERENCED_ELSEWHERE"
        elif record["classification"] == "DEFINITION_CANDIDATE":
            record["classification"] = "DEFINITION_CANDIDATE_AND_REFERENCED"


# ------------------------------------------------
# PASS F: generate hypothesis audit
# ------------------------------------------------

hyp_md = []

hyp_md.append("")
hyp_md.append("# 🧪 Hypothesis Dependency & Content Audit")
hyp_md.append("")
hyp_md.append(
    "This is an additive source-level audit of theorem/lemma hypotheses. "
    "It is intentionally separate from the existing architecture analysis."
)
hyp_md.append("")
hyp_md.append(
    "**Classification legend**  \n"
    "- `USED` — name appears more than once in the declaring block  \n"
    "- `DEFINITION_CANDIDATE` — equality-shaped, may be `rfl`-able  \n"
    "- `POSSIBLY_USED` — no textual re-occurrence, but type mentions other local hyps or looks like a bound  \n"
    "- `UNUSED_CANDIDATE` — no textual use and no soft signals (safe-ish to try deleting)  \n"
    "- `*_ELSEWHERE` / `*_AND_REFERENCED` — name also appears in other files"
)
hyp_md.append("")

# Group by module/theorem
grouped = defaultdict(list)
for record in hypothesis_records:
    grouped[(record["module"], record["theorem"])].append(record)

for (module, theorem), records in grouped.items():
    hyp_md.append(f"## `{module}.lean` — `{theorem}`")
    hyp_md.append("")
    hyp_md.append("| Hypothesis | Directly used | Used elsewhere | Classification |")
    hyp_md.append("|---|---:|---:|---|")

    for record in records:
        direct = "YES" if record["directly_used"] else "NO"
        if record["used_elsewhere"]:
            locations = ", ".join(
                f"{x['file']}:{x['line']}" for x in record["used_elsewhere"]
            )
        else:
            locations = "—"

        hyp_md.append(
            f"| `{record['hypothesis']}` | {direct} | {locations} | **{record['classification']}** |"
        )

    hyp_md.append("")
    hyp_md.append("<details>")
    hyp_md.append("<summary>Hypothesis types</summary>")
    hyp_md.append("")

    for record in records:
        hyp_md.append(f"**`{record['hypothesis']}`**")
        hyp_md.append("")
        hyp_md.append("```lean")
        hyp_md.append(record["type"] if record["type"] else "(type not recovered)")
        hyp_md.append("```")
        hyp_md.append("")

    hyp_md.append("</details>")
    hyp_md.append("")


# ------------------------------------------------
# PASS G: repository-level summary
# ------------------------------------------------

total_hypotheses = len(hypothesis_records)
used_count = sum(r["directly_used"] for r in hypothesis_records)
unused_candidate_count = sum(r["classification"] == "UNUSED_CANDIDATE" for r in hypothesis_records)
possibly_used_count = sum(r["classification"] == "POSSIBLY_USED" for r in hypothesis_records)
definition_candidates = sum("DEFINITION_CANDIDATE" in r["classification"] for r in hypothesis_records)
cross_referenced = sum(bool(r["used_elsewhere"]) for r in hypothesis_records)

hyp_md.append("## Repository Summary")
hyp_md.append("")
hyp_md.append("| Metric | Count |")
hyp_md.append("|---|---:|")
hyp_md.append(f"| Total hypotheses | {total_hypotheses} |")
hyp_md.append(f"| Directly used (textual) | {used_count} |")
hyp_md.append(f"| UNUSED_CANDIDATE | {unused_candidate_count} |")
hyp_md.append(f"| POSSIBLY_USED | {possibly_used_count} |")
hyp_md.append(f"| Definition candidates | {definition_candidates} |")
hyp_md.append(f"| Referenced elsewhere | {cross_referenced} |")
hyp_md.append("")


# ------------------------------------------------
# PASS H: candidate assumption set
# ------------------------------------------------

hyp_md.append("## Candidate Assumption Set")
hyp_md.append("")
hyp_md.append(
    "Hypotheses that are textually used (or marked POSSIBLY_USED) and are "
    "not obvious definitional identities. These are the ones most likely to "
    "carry real mathematical/physical content."
)
hyp_md.append("")

candidate_records = [
    r for r in hypothesis_records
    if r["classification"] in {
        "USED",
        "POSSIBLY_USED",
        "USED_AND_REFERENCED_ELSEWHERE",
        "USED_ELSEWHERE"
    }
]

if candidate_records:
    hyp_md.append("```text")
    for record in candidate_records:
        hyp_md.append(
            f"{record['module']}.{record['theorem']} :: {record['hypothesis']}"
        )
    hyp_md.append("```")
else:
    hyp_md.append("(none found)")

hyp_md.append("")


# ------------------------------------------------
# PASS I: warnings
# ------------------------------------------------

hyp_md.append("## ⚠️ Audit Limitations")
hyp_md.append("")
hyp_md.append("- `Directly used` means textual identifier occurrence in the source block.")
hyp_md.append("- It does **not** prove semantic necessity.")
hyp_md.append("- `DEFINITION_CANDIDATE` means equality-shaped; it does not prove `rfl` works.")
hyp_md.append("- `POSSIBLY_USED` is a conservative soft signal (mentions other local hyps or looks like a bound).")
hyp_md.append("- `UNUSED_CANDIDATE` is the only class that is relatively safe to try deleting.")
hyp_md.append("- `Used elsewhere` is only name-pattern matching across files (not true dependency).")
hyp_md.append("- Exact proof-term dependency requires Lean elaboration / metaprogramming.")
hyp_md.append("")


# ------------------------------------------------
# Append to document
# ------------------------------------------------

with open("theorem_architecture_hypo.md", "a", encoding="utf-8") as out:
    out.write("\n".join(hyp_md) + "\n")

print(
    f"✔ Hypothesis audit appended: "
    f"{total_hypotheses} hypotheses analyzed"
)

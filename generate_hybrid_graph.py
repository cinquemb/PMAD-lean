import os
import re

source_dir = "PMADLean"
files_to_scan = [f for f in os.listdir(source_dir) if f.endswith(".lean")]

# Keep your exact pattern and blacklists completely untouched
decl_pattern = re.compile(r'\b(?:theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_\.]+)')
tactics_blacklist = {'have', 'rw', 'using', 'unfold', 'of', 'block'}

file_declarations = {}
decl_to_full_id = {}
def_nodes = set()          
node_complexity = {}       

for filename in files_to_scan:
    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)
    file_declarations[module] = []
    
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
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

# Establish visual grouping boxes to force readable vertical stacking
module_meta = {
    "Axioms": {"title": "Axioms.lean (Foundations)", "color": "#1e3a8a", "stroke": "#3b82f6"},
    "Dynamics": {"title": "Dynamics.lean (Attractor Convergence)", "color": "#1e3a8a", "stroke": "#3b82f6"},
    "Probability": {"title": "Probability.lean (Born Rule & Bounds)", "color": "#064e3b", "stroke": "#10b981"},
    "Metrics": {"title": "Metrics.lean (Compliance Geometry)", "color": "#064e3b", "stroke": "#10b981"},
    "Renormalization": {"title": "Renormalization.lean (Scale Decay)", "color": "#3f1dcb", "stroke": "#8b5cf6"},
    "Vorticity": {"title": "Vorticity.lean (Spacetime Synthesis)", "color": "#7c2d12", "stroke": "#ea580c"},
    "Incompleteness": {"title": "Incompleteness.lean (Decoupled Limits)", "color": "#451a03", "stroke": "#b45309"}
}

mermaid_lines = [
    "graph TD",
    "    %% Scannable Layout Controls",
    "    classDef default fill:#111827,stroke:#374151,stroke-width:1px,color:#e5e7eb;",
    "    classDef heavyNode fill:#7f1d1d,stroke:#ef4444,stroke-width:2px,color:#fff;",
    "    classDef trivialNode fill:#1f2937,stroke:#9ca3af,stroke-width:1px,color:#9ca3af;",
    "    linkStyle default stroke:#4b5563,stroke-width:1px;"
]

heavy_node_ids = []
trivial_node_ids = []

# Generate clustered layout structural blocks
for module, decls in file_declarations.items():
    if not decls or module not in module_meta:
        continue
    meta = module_meta[module]
    
    mermaid_lines.append(f"\n    subgraph {module} [\"{meta['title']}\"]")
    # Force interior theorems to align Left-to-Right within the vertical module block
    mermaid_lines.append("        direction LR") 
    for short_name, full_id in decls:
        # Check if this node is a known structure/def or a proof type
        if full_id in def_nodes:
            mermaid_lines.append(f"        {full_id}(\"{short_name}\")") # Definitions get clean rounded capsules
        else:
            complexity = node_complexity.get(full_id, "heavy")
            if complexity == "trivial":
                mermaid_lines.append(f"        {full_id}[\"{short_name} ⟨id⟩\"]") # Simple proofs get gray tags
                trivial_node_ids.append(full_id)
            else:
                mermaid_lines.append(f"        {full_id}[[\"{short_name} 🔥\"]]") # Stiff analytic proofs keep the fire stadium box
                heavy_node_ids.append(full_id)
    mermaid_lines.append("    end")
    mermaid_lines.append(f"    style {module} fill:{meta['color']},stroke:{meta['stroke']},stroke-width:2px,color:#fff;")

# Map edge connections cleanly
seen_edges = set()
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
        if not lines:
            continue
        # BUG FIX: Target strictly the first string item index in the code lines array slice
        header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
        if not header_match:
            continue
            
        src_short = header_match.group(1)
        if src_short in tactics_blacklist:
            continue
        src_full = f"{module}_{src_short}"
        
        # FIX: Check if the block contains simple termination tokens like rfl or le_refl
        if src_full not in def_nodes:
            body_lower = block.lower()
            if 'rfl' in body_lower or 'le_refl' in body_lower:
                node_complexity[src_full] = "trivial"
            else:
                node_complexity[src_full] = "heavy"
        
        tokens = re.findall(r'\b([A-Za-z0-9_\.]+)\b', block)
        for token in tokens:
            if token in decl_to_full_id and token != src_short:
                tgt_full = decl_to_full_id[token]
                
                # Check for cross-module edge transformations
                is_cross = token not in [d[0] for d in file_declarations[module]]
                
                # Make cross-module connections visually distinct and thicker
                edge_style = " ==X-Module==> " if is_cross else " --> "
                edge = f"    {src_full}{edge_style}{tgt_full}"
                
                if edge not in seen_edges:
                    mermaid_lines.append(edge)
                    seen_edges.add(edge)

# Append specialized class mappings safely to the bottom of the line block array
if heavy_node_ids:
    mermaid_lines.append(f"    class {','.join(heavy_node_ids)} heavyNode;")
if trivial_node_ids:
    mermaid_lines.append(f"    class {','.join(trivial_node_ids)} trivialNode;")

with open("theorem_architecture.md", "w", encoding="utf-8") as out:
    out.write("\n".join(mermaid_lines) + "\n")

print("✔ Optimized high-scannability graph written to theorem_architecture.md")


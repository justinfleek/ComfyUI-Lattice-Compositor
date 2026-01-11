# /type-audit Command

Run a comprehensive type audit of the codebase.

## Usage
User says: "/type-audit" or "audit types"

## Actions

### 1. Generate Counts
```bash
echo "=== TYPE ISSUES ==="
echo "as any: $(grep -rn 'as any' src/ --include='*.ts' | grep -v node_modules | wc -l)"
echo "as unknown as: $(grep -rn 'as unknown as' src/ --include='*.ts' | grep -v node_modules | wc -l)"
echo ": any: $(grep -rn ': any' src/ --include='*.ts' | grep -v node_modules | grep -v '.d.ts' | wc -l)"
echo "@ts-ignore: $(grep -rn '@ts-ignore' src/ --include='*.ts' | grep -v node_modules | wc -l)"
```

### 2. Categorize by Location
- services/ai/ → INPUT BOUNDARY
- services/export/ → INPUT BOUNDARY
- engine/animation/, engine/particles/ → NUMERIC
- stores/, composables/ → INTERNAL

### 3. Output Priority List
Sort by: INPUT BOUNDARIES first, then NUMERIC, then INTERNAL

### 4. Save to File
```bash
# Save to ui/type-audit/AUDIT-$(date +%Y%m%d).md
```

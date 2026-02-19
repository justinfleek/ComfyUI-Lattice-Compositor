# Split MASTER_AUDIT.md by major sections
$lines = Get-Content MASTER_AUDIT.md

# Find section boundaries
$sections = @{
    "instructions" = @{start=0; end=55}
    "bugs" = @{start=56; end=138}
    "particle-audit" = @{start=139; end=585}
    "coverage" = @{start=586; end=945}
    "services" = @{start=946; end=1354}
    "engine" = @{start=1355; end=1454}
    "stores" = @{start=1455; end=1620}
    "lattice" = @{start=1621; end=1700}
    "pipelines" = @{start=1701; end=$lines.Count}
}

foreach ($name in $sections.Keys) {
    $s = $sections[$name]
    $content = $lines[$s.start..$s.end] -join "`n"
    $outFile = "docs\audit\$name.md"
    "# Audit: $name`n`n$content" | Out-File -FilePath $outFile -Encoding utf8
    Write-Host "Created: $outFile ($($s.end - $s.start + 1) lines)"
}

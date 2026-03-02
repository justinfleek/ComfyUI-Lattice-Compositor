$lines = Get-Content "docs\audit\pipelines.md"

$splits = @{
    "pipelines-overview" = @{start=0; end=199}
    "pipelines-layers" = @{start=200; end=450}
    "pipelines-browser" = @{start=451; end=730}
    "pipelines-coverage" = @{start=731; end=1070}
    "pipelines-status" = @{start=1071; end=$lines.Count-1}
}

foreach ($name in $splits.Keys) {
    $s = $splits[$name]
    $content = $lines[$s.start..$s.end] -join "`n"
    $outFile = "docs\audit\$name.md"
    $content | Out-File -FilePath $outFile -Encoding utf8
    Write-Host "Created: $outFile ($($s.end - $s.start + 1) lines)"
}

# Remove old pipelines.md
Remove-Item "docs\audit\pipelines.md"
Write-Host "Removed: docs\audit\pipelines.md"

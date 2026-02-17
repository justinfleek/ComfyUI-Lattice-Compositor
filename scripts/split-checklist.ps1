# Split MASTER_CHECKLIST.md by domain
$content = Get-Content MASTER_CHECKLIST.md -Raw
$sections = $content -split "(?m)(?=^## )" | Where-Object { $_ -match "^## " }

$domains = @{}
foreach ($section in $sections) {
    $firstLine = ($section -split "`n")[0]
    $domain = ($firstLine -replace "^## ", "") -split "/" | Select-Object -First 1
    if (-not $domains[$domain]) { $domains[$domain] = @() }
    $domains[$domain] += $section
}

foreach ($domain in $domains.Keys) {
    $outFile = "docs\checklists\$domain.md"
    $domainContent = "# Checklist: $domain`n`n" + ($domains[$domain] -join "`n")
    $domainContent | Out-File -FilePath $outFile -Encoding utf8
    Write-Host "Created: $outFile ($(($domains[$domain]).Count) sections)"
}

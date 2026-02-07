# PowerShell script to set up Claude Code MCP server configuration
# Run this script to configure Claude Code to use the Straylight Protocol MCP server

$ErrorActionPreference = "Stop"

# Get the project root directory
$projectRoot = $PSScriptRoot | Split-Path -Parent
$mcpServerPath = Join-Path $projectRoot ".claude\straylight-mcp.js"

# Verify MCP server exists
if (-not (Test-Path $mcpServerPath)) {
    Write-Error "MCP server not found at: $mcpServerPath"
    exit 1
}

# Convert to absolute path
$mcpServerPath = (Resolve-Path $mcpServerPath).Path

# Determine Claude config directory based on OS
if ($IsWindows -or $env:OS -eq "Windows_NT") {
    $claudeConfigDir = Join-Path $env:USERPROFILE ".claude"
    $claudeConfigFile = Join-Path $claudeConfigDir "claude_desktop_config.json"
} elseif ($IsMacOS) {
    $claudeConfigDir = Join-Path $env:HOME "Library/Application Support/Claude"
    $claudeConfigFile = Join-Path $claudeConfigDir "claude_desktop_config.json"
} else {
    # Linux
    $claudeConfigDir = Join-Path $env:HOME ".claude"
    $claudeConfigFile = Join-Path $claudeConfigDir "claude_desktop_config.json"
}

# Create config directory if it doesn't exist
if (-not (Test-Path $claudeConfigDir)) {
    New-Item -ItemType Directory -Path $claudeConfigDir -Force | Out-Null
    Write-Host "Created Claude config directory: $claudeConfigDir"
}

# Read existing config or create new one
$config = @{}
if (Test-Path $claudeConfigFile) {
    try {
        $existingConfig = Get-Content $claudeConfigFile -Raw | ConvertFrom-Json
        $config = $existingConfig | ConvertTo-Json -Depth 10 | ConvertFrom-Json
    } catch {
        Write-Warning "Could not parse existing config, creating new one"
        $config = @{}
    }
}

# Ensure mcpServers object exists
if (-not $config.mcpServers) {
    $config | Add-Member -MemberType NoteProperty -Name "mcpServers" -Value @{}
}

# Add or update straylight server config
$config.mcpServers.straylight = @{
    command = "node"
    args = @($mcpServerPath)
}

# Write config file
$configJson = $config | ConvertTo-Json -Depth 10
Set-Content -Path $claudeConfigFile -Value $configJson -Encoding UTF8

Write-Host "✅ Claude Code MCP configuration updated!"
Write-Host "   Config file: $claudeConfigFile"
Write-Host "   MCP server: $mcpServerPath"
Write-Host ""
Write-Host "⚠️  Please restart Claude Code for changes to take effect."

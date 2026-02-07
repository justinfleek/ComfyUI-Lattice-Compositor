#!/usr/bin/env node
/**
 * Generate detailed validation reports from validation results
 * Supports HTML, Markdown, and JSON output formats
 */

import { readFileSync, writeFileSync, existsSync } from 'fs';
import { resolve } from 'path';

/**
 * Generate HTML report
 */
function generateHTMLReport(results) {
  const html = `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Straylight Protocol Validation Report</title>
  <style>
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, Cantarell, sans-serif;
      line-height: 1.6;
      max-width: 1200px;
      margin: 0 auto;
      padding: 20px;
      background: #f5f5f5;
    }
    .container {
      background: white;
      padding: 30px;
      border-radius: 8px;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    h1 {
      color: #2c3e50;
      border-bottom: 3px solid #3498db;
      padding-bottom: 10px;
    }
    h2 {
      color: #34495e;
      margin-top: 30px;
      border-bottom: 2px solid #ecf0f1;
      padding-bottom: 5px;
    }
    .summary {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
      gap: 20px;
      margin: 20px 0;
    }
    .stat-card {
      background: #f8f9fa;
      padding: 20px;
      border-radius: 6px;
      border-left: 4px solid #3498db;
    }
    .stat-card.success {
      border-left-color: #27ae60;
    }
    .stat-card.error {
      border-left-color: #e74c3c;
    }
    .stat-card.warning {
      border-left-color: #f39c12;
    }
    .stat-value {
      font-size: 2em;
      font-weight: bold;
      color: #2c3e50;
    }
    .stat-label {
      color: #7f8c8d;
      font-size: 0.9em;
      text-transform: uppercase;
      letter-spacing: 1px;
    }
    table {
      width: 100%;
      border-collapse: collapse;
      margin: 20px 0;
    }
    th, td {
      padding: 12px;
      text-align: left;
      border-bottom: 1px solid #ecf0f1;
    }
    th {
      background: #34495e;
      color: white;
      font-weight: 600;
    }
    tr:hover {
      background: #f8f9fa;
    }
    .rule-badge {
      display: inline-block;
      padding: 4px 8px;
      border-radius: 4px;
      font-size: 0.85em;
      font-weight: 600;
      background: #e74c3c;
      color: white;
    }
    .rule-badge.warning {
      background: #f39c12;
    }
    .file-list {
      max-height: 400px;
      overflow-y: auto;
      border: 1px solid #ecf0f1;
      border-radius: 4px;
      padding: 10px;
    }
    .file-item {
      padding: 8px;
      margin: 4px 0;
      background: #f8f9fa;
      border-radius: 4px;
      font-family: 'Courier New', monospace;
      font-size: 0.9em;
    }
    .error-item {
      border-left: 3px solid #e74c3c;
    }
    .warning-item {
      border-left: 3px solid #f39c12;
    }
    .timestamp {
      color: #7f8c8d;
      font-size: 0.9em;
      margin-top: 20px;
    }
  </style>
</head>
<body>
  <div class="container">
    <h1>🔍 Straylight Protocol Validation Report</h1>
    <p class="timestamp">Generated: ${new Date().toLocaleString()}</p>
    
    <div class="summary">
      <div class="stat-card success">
        <div class="stat-value">${results.passed}</div>
        <div class="stat-label">Files Passed</div>
      </div>
      <div class="stat-card error">
        <div class="stat-value">${results.failed}</div>
        <div class="stat-label">Files Failed</div>
      </div>
      <div class="stat-card warning">
        <div class="stat-value">${results.warnings}</div>
        <div class="stat-label">Total Warnings</div>
      </div>
      <div class="stat-card">
        <div class="stat-value">${results.total}</div>
        <div class="stat-label">Total Files</div>
      </div>
      <div class="stat-card">
        <div class="stat-value">${(results.duration / 1000).toFixed(2)}s</div>
        <div class="stat-label">Duration</div>
      </div>
    </div>
    
    ${Object.keys(results.ruleViolations).length > 0 ? `
    <h2>📋 Violations by Rule</h2>
    <table>
      <thead>
        <tr>
          <th>Rule ID</th>
          <th>Violations</th>
          <th>Files Affected</th>
        </tr>
      </thead>
      <tbody>
        ${Object.entries(results.ruleViolations)
          .sort((a, b) => b[1].count - a[1].count)
          .map(([rule, data]) => `
        <tr>
          <td><span class="rule-badge ${rule.includes('WARNING') ? 'warning' : ''}">${rule}</span></td>
          <td>${data.count}</td>
          <td>${data.files.length}</td>
        </tr>
          `).join('')}
      </tbody>
    </table>
    ` : '<p>✅ No violations found!</p>'}
    
    ${results.files.filter(f => !f.valid || f.errors.length > 0).length > 0 ? `
    <h2>❌ Files with Errors</h2>
    <div class="file-list">
      ${results.files
        .filter(f => !f.valid || f.errors.length > 0)
        .map(file => `
      <div class="file-item error-item">
        <strong>${file.path}</strong> (${file.type})
        <ul>
          ${file.errors.map(e => `<li>Line ${e.line}: [${e.rule}] ${e.message}</li>`).join('')}
        </ul>
      </div>
      `).join('')}
    </div>
    ` : ''}
    
    ${results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length > 0 ? `
    <h2>⚠️ Files with Warnings</h2>
    <div class="file-list">
      ${results.files
        .filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0)
        .slice(0, 50)
        .map(file => `
      <div class="file-item warning-item">
        <strong>${file.path}</strong> (${file.type}) - ${file.warnings.length} warning(s)
      </div>
      `).join('')}
      ${results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length > 50 ? 
        `<p><em>... and ${results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length - 50} more files</em></p>` : ''}
    </div>
    ` : ''}
  </div>
</body>
</html>`;
  
  return html;
}

/**
 * Generate Markdown report
 */
function generateMarkdownReport(results) {
  const md = `# Straylight Protocol Validation Report

**Generated:** ${new Date().toLocaleString()}

## Summary

| Metric | Value |
|--------|-------|
| Total Files | ${results.total} |
| ✅ Passed | ${results.passed} |
| ❌ Failed | ${results.failed} |
| ⚠️ Warnings | ${results.warnings} |
| ⏱️ Duration | ${(results.duration / 1000).toFixed(2)}s |

## Violations by Rule

${Object.keys(results.ruleViolations).length > 0 ? Object.entries(results.ruleViolations)
  .sort((a, b) => b[1].count - a[1].count)
  .map(([rule, data]) => `### ${rule}
- **Violations:** ${data.count}
- **Files Affected:** ${data.files.length}
- **Files:**
${data.files.slice(0, 10).map(f => `  - \`${f}\``).join('\n')}${data.files.length > 10 ? `\n  - ... and ${data.files.length - 10} more` : ''}
`).join('\n') : '✅ No violations found!'}

## Files with Errors

${results.files.filter(f => !f.valid || f.errors.length > 0).length > 0 ? results.files
  .filter(f => !f.valid || f.errors.length > 0)
  .map(file => `### \`${file.path}\` (${file.type})
${file.errors.map(e => `- Line ${e.line}: [${e.rule}] ${e.message}`).join('\n')}
`).join('\n') : '✅ No files with errors!'}

## Files with Warnings Only

${results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length > 0 ? results.files
  .filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0)
  .slice(0, 50)
  .map(file => `- \`${file.path}\` (${file.type}) - ${file.warnings.length} warning(s)`)
  .join('\n') + (results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length > 50 ? `\n- ... and ${results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0).length - 50} more files` : '') : '✅ No files with warnings!'}
`;
  
  return md;
}

/**
 * Main execution
 */
function main() {
  const inputFile = process.argv[2];
  const outputFormat = process.argv[3] || 'markdown'; // 'html', 'markdown', 'json'
  const outputFile = process.argv[4];
  
  if (!inputFile) {
    console.error('Usage: node generate-validation-report.js <input-json> [format] [output-file]');
    console.error('  format: html, markdown, json (default: markdown)');
    process.exit(1);
  }
  
  const inputPath = resolve(inputFile);
  
  if (!existsSync(inputPath)) {
    console.error(`❌ Error: Input file not found: ${inputPath}`);
    process.exit(1);
  }
  
  let results;
  try {
    const content = readFileSync(inputPath, 'utf-8');
    results = JSON.parse(content);
  } catch (error) {
    console.error(`❌ Error reading input file: ${error.message}`);
    process.exit(1);
  }
  
  let output;
  let extension;
  
  switch (outputFormat.toLowerCase()) {
    case 'html':
      output = generateHTMLReport(results);
      extension = '.html';
      break;
    case 'markdown':
    case 'md':
      output = generateMarkdownReport(results);
      extension = '.md';
      break;
    case 'json':
      output = JSON.stringify(results, null, 2);
      extension = '.json';
      break;
    default:
      console.error(`❌ Error: Unknown format: ${outputFormat}`);
      console.error('Supported formats: html, markdown, json');
      process.exit(1);
  }
  
  if (outputFile) {
    const outputPath = resolve(outputFile);
    writeFileSync(outputPath, output, 'utf-8');
    console.log(`✅ Report generated: ${outputPath}`);
  } else {
    console.log(output);
  }
}

main();

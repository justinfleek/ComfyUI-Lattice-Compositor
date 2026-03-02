'use client'

import { useEffect, useState } from 'react'

export default function LeanPage() {
  const [content, setContent] = useState<string>('')
  const [loading, setLoading] = useState(true)

  useEffect(() => {
    fetch('/assets/VillaStraylight.lean')
      .then(res => res.text())
      .then(text => {
        setContent(text)
        setLoading(false)
      })
      .catch(() => {
        setContent('-- Error loading file')
        setLoading(false)
      })
  }, [])

  return (
    <div>
      <div className="mb-8">
        <h1 className="text-xl font-medium text-text mb-2">
          VillaStraylight.lean
        </h1>
        <p className="text-muted-foreground text-sm">
          21 theorems from nvfuser. 0 sorry. 1575 lines of Lean 4.
        </p>
      </div>

      {loading ? (
        <div className="text-muted-foreground">loading...</div>
      ) : (
        <div className="bg-[#0d1117] border border-border rounded overflow-x-auto">
          <pre className="p-4 text-[0.8rem] leading-relaxed font-mono">
            <code>
              {/* eslint-disable-next-line react/no-array-index-key */}
              {content.split('\n').map((line, i) => (
                <Line key={i.toString()} line={line} />
              ))}
            </code>
          </pre>
        </div>
      )}

      <div className="mt-6 text-sm">
        <a 
          href="/assets/VillaStraylight.lean" 
          download
          className="text-primary hover:underline"
        >
          download raw
        </a>
      </div>
    </div>
  )
}

function Line({ line }: { line: string }) {
  const trimmed = line.trim()
  
  // Documentation blocks
  if (trimmed.startsWith('/-!') || trimmed.startsWith('-/') || 
      trimmed.startsWith('━') || trimmed.startsWith('//') ||
      trimmed.startsWith('—')) {
    return <div style={{ color: '#596775' }}>{line}</div>
  }
  
  // Comments
  if (trimmed.startsWith('--')) {
    return <div style={{ color: '#596775' }}>{line}</div>
  }
  
  // Tokenize the rest
  return <div>{highlightLine(line)}</div>
}

function highlightLine(line: string): React.ReactNode[] {
  const tokens: React.ReactNode[] = []
  let remaining = line
  let key = 0
  
  while (remaining.length > 0) {
    // String literal
    if (remaining[0] === '"') {
      const end = findEndQuote(remaining.slice(1))
      const str = remaining.slice(0, end + 2)
      tokens.push(<span key={key++} style={{ color: '#7ee787' }}>{str}</span>)
      remaining = remaining.slice(end + 2)
      continue
    }
    
    // Match word
    const match = remaining.match(/^(\w+)/)
    if (match) {
      const word = match[1]
      tokens.push(<span key={key++} style={{ color: getWordColor(word) }}>{word}</span>)
      remaining = remaining.slice(word.length)
      continue
    }
    
    // Single char
    tokens.push(<span key={key++} style={{ color: '#b6e3ff' }}>{remaining[0]}</span>)
    remaining = remaining.slice(1)
  }
  
  return tokens
}

function findEndQuote(s: string): number {
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '"') return i
    if (s[i] === '\\') i++
  }
  return s.length
}

function getWordColor(word: string): string {
  const keywords = ['import', 'where', 'if', 'then', 'else', 'let', 'in', 'do', 'return',
    'match', 'with', 'fun', 'by', 'have', 'show', 'from', 'calc', 'at',
    'intro', 'exact', 'apply', 'rw', 'simp', 'omega', 'ring', 'constructor',
    'cases', 'induction', 'rcases', 'obtain', 'refine', 'use', 'ext',
    'push_neg', 'by_contra', 'by_cases', 'subst', 'conv']
  
  const defKeywords = ['def', 'theorem', 'lemma', 'structure', 'inductive', 'class', 'instance',
    'namespace', 'end', 'section', 'variable', 'open', 'export', 'deriving',
    'private', 'protected', 'partial', 'unsafe', 'noncomputable']
  
  if (keywords.includes(word)) return '#54aeff'
  if (defKeywords.includes(word)) return '#d29922'
  if (word[0] >= 'A' && word[0] <= 'Z') return '#d2a8ff'
  if (word[0] >= '0' && word[0] <= '9') return '#f0883e'
  return '#b6e3ff'
}

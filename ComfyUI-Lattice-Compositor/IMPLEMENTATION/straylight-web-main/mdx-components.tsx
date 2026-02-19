import type { MDXComponents } from 'mdx/types'

export function useMDXComponents(components: MDXComponents): MDXComponents {
  return {
    // Style headings
    h1: ({ children }) => (
      <h1 className="text-xl font-medium text-text mb-4">{children}</h1>
    ),
    h2: ({ children }) => (
      <h2 className="text-lg font-medium text-text mt-8 mb-4">{children}</h2>
    ),
    h3: ({ children }) => (
      <h3 className="text-base font-medium text-text mt-6 mb-3">{children}</h3>
    ),
    h4: ({ children }) => (
      <h4 className="text-sm font-medium text-text mt-4 mb-2">{children}</h4>
    ),
    // Paragraphs
    p: ({ children }) => (
      <p className="text-muted-foreground mb-4 leading-relaxed">{children}</p>
    ),
    // Lists
    ul: ({ children }) => (
      <ul className="list-disc list-inside text-muted-foreground mb-4 space-y-1">{children}</ul>
    ),
    ol: ({ children }) => (
      <ol className="list-decimal list-inside text-muted-foreground mb-4 space-y-1">{children}</ol>
    ),
    li: ({ children }) => (
      <li className="text-muted-foreground">{children}</li>
    ),
    // Code
    code: ({ children }) => (
      <code className="bg-card px-1.5 py-0.5 rounded text-primary text-sm font-mono">{children}</code>
    ),
    pre: ({ children }) => (
      <pre className="bg-[#0d1117] border border-border rounded p-4 overflow-x-auto mb-4 text-sm">{children}</pre>
    ),
    // Blockquote
    blockquote: ({ children }) => (
      <blockquote className="border-l-2 border-primary pl-4 italic text-muted-foreground mb-4">{children}</blockquote>
    ),
    // Links
    a: ({ href, children }) => (
      <a href={href} className="text-primary hover:underline">{children}</a>
    ),
    // Horizontal rule
    hr: () => (
      <hr className="border-border my-8" />
    ),
    // Strong/emphasis
    strong: ({ children }) => (
      <strong className="text-text font-medium">{children}</strong>
    ),
    em: ({ children }) => (
      <em className="italic">{children}</em>
    ),
    ...components,
  }
}

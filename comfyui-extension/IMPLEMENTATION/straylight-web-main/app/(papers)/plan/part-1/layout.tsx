import type { Metadata } from 'next'

export const metadata: Metadata = {
  title: 'The Villa Straylight Papers // straylight //',
  description: "Jensen's Razor and the malevolent combinatorics of CUDA architecture.",
}

export default function PaperLayout({
  children,
}: {
  children: React.ReactNode
}) {
  return (
    <div className="min-h-screen bg-background" data-theme="ono-memphis">
      {/* Scanline overlay */}
      <div 
        className="pointer-events-none fixed inset-0 z-50"
        style={{
          background: 'repeating-linear-gradient(0deg, transparent, transparent 2px, rgba(0,0,0,0.03) 2px, rgba(0,0,0,0.03) 4px)',
        }}
      />
      
      {/* Header */}
      {/* eslint-disable-next-line */}
      <header className="border-b border-border">
        <div className="max-w-4xl mx-auto px-8 py-6 flex items-center justify-between">
          <a href="/" className="text-text hover:text-primary transition-colors font-medium">
            {"// straylight //"}
          </a>
          <div className="flex items-center gap-6 text-sm">
            <a href="/plan" className="text-muted-foreground hover:text-text transition-colors">
              .plan
            </a>
            {/* Locked theme picker - just for show */}
            <div className="flex items-center gap-2 text-muted-foreground/50 cursor-not-allowed" title="theme locked: typographical ultraviolence">
              <span className="text-xs">ono-memphis</span>
              <svg className="w-3 h-3" fill="currentColor" viewBox="0 0 20 20" aria-hidden="true">
                <path fillRule="evenodd" d="M5 9V7a5 5 0 0110 0v2a2 2 0 012 2v5a2 2 0 01-2 2H5a2 2 0 01-2-2v-5a2 2 0 012-2zm8-2v2H7V7a3 3 0 016 0z" clipRule="evenodd" />
              </svg>
            </div>
          </div>
        </div>
      </header>

      {/* Content */}
      <main className="max-w-4xl mx-auto px-8 py-12">
        <article className="paper-content">
          {children}
        </article>
      </main>

      {/* Footer */}
      <footer className="border-t border-border mt-24">
        <div className="max-w-4xl mx-auto px-8 py-8 text-center text-sm text-muted-foreground">
          <p>the blade studied you back</p>
        </div>
      </footer>
    </div>
  )
}

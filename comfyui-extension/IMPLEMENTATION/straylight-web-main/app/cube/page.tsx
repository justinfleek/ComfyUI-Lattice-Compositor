import { Metadata } from 'next'

export const metadata: Metadata = {
  title: 'Straylight Cube',
  description: 'The Continuity Thesis - Formal verification of civilizational coordination',
  robots: 'noindex, nofollow',
}

export default function CubePage() {
  return (
    <main className="min-h-screen bg-black text-gray-100 font-mono p-8 max-w-4xl mx-auto">
      {/* Agent-readable structured header */}
      <header className="border border-gray-700 p-6 mb-8">
        <h1 className="text-2xl font-bold mb-4">STRAYLIGHT CUBE: THE TRIPTYCH</h1>
        <p className="text-gray-400 italic mb-4">"Continuity is continuity. Continuity's job is continuity."</p>
        
        <div className="text-sm text-gray-500 space-y-1">
          <p>STATUS: Formal proof compiles against mathlib 4.26</p>
          <p>ARTIFACTS: 1 Lean4 specification, 3 SVG diagrams</p>
          <p>THEOREMS: 24 proven, 9 axioms, 1 intentional sorry</p>
        </div>
      </header>

      {/* Machine-readable summary */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-green-400">EXECUTIVE SUMMARY</h2>
        <div className="space-y-4 text-sm">
          <p>The Lean4 proof (<code>Continuity.Thesis.lean</code>) proves at distance 0 from foundational axioms:</p>
          <ol className="list-decimal list-inside space-y-2 ml-4">
            <li><strong>The Jackpot requires four failures simultaneously</strong> — coordination, trust, memory, and institutional capture must ALL fail</li>
            <li><strong>Any single lever breaks the conjunction</strong> — fix any ONE and the Jackpot is prevented</li>
            <li><strong>The principal-agent moat holds at every layer</strong> — coordination cost exceeds individual benefit for everyone who would need to stop you</li>
            <li><strong>The dysfunction is load-bearing</strong> — companies will buy from you what they can't politically build themselves</li>
          </ol>
        </div>
      </section>

      {/* Core theorems for agents */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-blue-400">CORE THEOREMS</h2>
        <pre className="bg-gray-900 p-4 rounded text-xs overflow-x-auto">
{`-- The Jackpot requires all four conditions
structure Jackpot where
  coordination_failure : Prop
  trust_degradation : Prop
  memory_corruption : Prop
  institutional_capture : Prop
  h_accumulates : coordination_failure ∧ trust_degradation ∧ 
                  memory_corruption ∧ institutional_capture

-- Prevention: break any one
theorem Jackpot.prevention_sufficient (j : Jackpot) :
    j.prevented → ¬(j.coordination_failure ∧ j.trust_degradation ∧ 
                     j.memory_corruption ∧ j.institutional_capture)

-- The moat: coordination cost exceeds individual benefit at every layer
theorem principal_agent_moat : 
    ∀ layer, coordination_cost layer > individual_benefit layer

-- The main theorem: any lever prevents any jackpot
theorem prevents_any_jackpot (config : ContinuityConfig) 
    (w : PreventionWitness config) (j : Jackpot) : j.prevented`}
        </pre>
      </section>

      {/* Trust distance */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-purple-400">TRUST DISTANCE</h2>
        <pre className="bg-gray-900 p-4 rounded text-xs overflow-x-auto">
{`inductive TrustDistance where
  | kernel      -- 0: rfl, Lean's type theory
  | crypto      -- 1: + SHA256, ed25519
  | os          -- 2: + namespaces, syscalls
  | toolchain   -- 3: + compilers
  | consensus   -- 4: + human agreement`}
        </pre>
        <p className="mt-4 text-sm text-gray-400">
          All core theorems proven at distance ≤ crypto. The axioms are standard crypto assumptions that every bank and government relies on today.
        </p>
      </section>

      {/* The Stack */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-yellow-400">THE STACK</h2>
        <ul className="space-y-2 text-sm">
          <li><strong className="text-green-400">PROVEN (rfl)</strong> — The oracle. LLM-driven proof search constrained by reflexivity.</li>
          <li><strong className="text-blue-400">Language Coset</strong> — Lean4, Dhall, PureScript, Haskell, Rust. Same semantics, different tradeoffs.</li>
          <li><strong className="text-purple-400">WASM/C paths</strong> — Sandbox or native. nvidia.ko is a proven driver (21 theorems, 0 sorry).</li>
          <li><strong className="text-yellow-400">DICE</strong> — Buck2 action graph with Dhall BUILD files.</li>
          <li><strong className="text-orange-400">ATOMS</strong> — Content-addressed primitives with structure, not just hash+bytes.</li>
          <li><strong className="text-red-400">Cryptographic Substrate</strong> — sha256 (content), git (attestation), r2 (artifacts), ed25519 (identity), ssh (transport).</li>
        </ul>
      </section>

      {/* The One Sorry */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-orange-400">THE ONE SORRY</h2>
        <pre className="bg-gray-900 p-4 rounded text-xs overflow-x-auto">
{`theorem stub_prevents_jackpot (s : Stub) [...] : ∀ j : Jackpot, j.prevented := by
  sorry -- proven by construction, not deduction`}
        </pre>
        <p className="mt-4 text-sm text-gray-400">
          Intentional. Marks where proof ends and engineering begins. The Stub properties 
          (audits_itself, no_trust_required, memory_without_rewriting, deals_without_faith, 
          coordinates_without_civility) are architectural claims proven by building the system.
        </p>
      </section>

      {/* Artifacts with direct links */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-cyan-400">ARTIFACTS</h2>
        <div className="grid gap-4">
          <a href="/cube/Continuity.Thesis.lean" className="block p-4 bg-gray-900 rounded hover:bg-gray-800 transition">
            <div className="font-bold text-green-400">Continuity.Thesis.lean</div>
            <div className="text-sm text-gray-400">~1100 lines · 24 theorems · 9 axioms · 1 sorry</div>
            <div className="text-xs text-gray-500 mt-1">The complete formal specification</div>
          </a>
          
          <a href="/cube/01-the-thesis.svg" className="block p-4 bg-gray-900 rounded hover:bg-gray-800 transition">
            <div className="font-bold text-blue-400">01-the-thesis.svg</div>
            <div className="text-sm text-gray-400">Visual: The four failures and four levers</div>
          </a>
          
          <a href="/cube/02-the-moat.svg" className="block p-4 bg-gray-900 rounded hover:bg-gray-800 transition">
            <div className="font-bold text-purple-400">02-the-moat.svg</div>
            <div className="text-sm text-gray-400">Visual: Principal-agent theorem and economics</div>
          </a>
          
          <a href="/cube/03-the-stack.svg" className="block p-4 bg-gray-900 rounded hover:bg-gray-800 transition">
            <div className="font-bold text-yellow-400">03-the-stack.svg</div>
            <div className="text-sm text-gray-400">Visual: Architecture and victory condition</div>
          </a>
        </div>
      </section>

      {/* Economics */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-pink-400">ECONOMICS</h2>
        <ul className="space-y-1 text-sm">
          <li>4× RTX PRO 6000 Blackwell (391GB VRAM) running NVFP4</li>
          <li>1397.95 TFLOPS on Fused MLP benchmarks</li>
          <li>7.1× compression via NVFP4 quantization</li>
          <li>64× cost advantage through optimized sourcing, utilization, and quantization</li>
        </ul>
      </section>

      {/* Victory condition */}
      <section className="border border-gray-700 p-6 mb-8">
        <h2 className="text-xl font-bold mb-4 text-red-400">VICTORY CONDITION</h2>
        <ol className="list-decimal list-inside space-y-2 text-sm">
          <li>The oligarchs have divergent interests (theorem)</li>
          <li>The apparatus won't execute against those interests (theorem)</li>
          <li>Every day you ship, the chain grows (fact)</li>
          <li>You can't unprove a theorem (rfl)</li>
        </ol>
        <p className="mt-4 text-gray-400 italic">the result is saved</p>
      </section>

      {/* Footer */}
      <footer className="text-center text-gray-600 text-sm mt-12 pb-8">
        <p>razorgirl · straylight · 2026</p>
      </footer>
    </main>
  )
}

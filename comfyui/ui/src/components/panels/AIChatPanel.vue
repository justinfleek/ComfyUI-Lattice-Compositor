<!--
  @component AIChatPanel
  @description AI-powered natural language interface for motion graphics.
  Chat with GPT-4o or Claude Sonnet to create animations:
  - Natural language animation commands
  - Iterative refinement ("make it faster", "add glow")
  - Full compositor schema understanding
  - Real-time layer/keyframe creation

  @features
  - Model selection (GPT-4o, Claude Sonnet)
  - Conversation history with clear function
  - Streaming response display
  - Error handling with retry
  - Keyboard submit (Enter to send)

  @examples
  - "Fade in the title over 1 second"
  - "Create floating particles that drift upward"
  - "Make the selected layer bounce in from the left"
  - "Add a glow effect to all text layers"

  @requires OPENAI_API_KEY or ANTHROPIC_API_KEY environment variable
-->
<template>
  <div class="ai-chat-panel" role="region" aria-label="AI Compositor Agent">
    <div class="panel-header">
      <span class="panel-title">AI Agent</span>
      <div class="header-actions">
        <select
          v-model="selectedModel"
          class="model-selector"
          aria-label="Select AI model"
        >
          <option value="gpt-4o">GPT-4o</option>
          <option value="claude-sonnet">Claude Sonnet</option>
        </select>
        <button
          class="clear-btn"
          @click="clearHistory"
          title="Clear conversation"
          aria-label="Clear conversation history"
        >
          Clear
        </button>
      </div>
    </div>

    <div class="chat-messages" ref="messagesContainer">
      <!-- Welcome message -->
      <div v-if="messages.length === 0" class="welcome-message">
        <div class="welcome-icon">AI</div>
        <h3>AI Compositor Agent</h3>
        <p>
          Describe the motion graphics you want to create, and I'll build it for you.
        </p>
        <div class="example-prompts">
          <button
            v-for="example in examplePrompts"
            :key="example"
            class="example-btn"
            @click="useExample(example)"
          >
            {{ example }}
          </button>
        </div>
      </div>

      <!-- Message history -->
      <div
        v-for="(message, index) in messages"
        :key="index"
        class="message"
        :class="message.role"
      >
        <div class="message-header">
          <span class="role-label">{{ message.role === 'user' ? 'You' : 'AI Agent' }}</span>
          <span class="timestamp">{{ formatTime(message.timestamp) }}</span>
        </div>
        <div class="message-content" v-html="formatContent(message.content)"></div>

        <!-- Tool calls display -->
        <div v-if="message.toolCalls && message.toolCalls.length > 0" class="tool-calls">
          <div class="tool-calls-header">Actions taken:</div>
          <div
            v-for="(call, i) in message.toolCalls"
            :key="i"
            class="tool-call"
          >
            <span class="tool-icon">{{ getToolIcon(call.name) }}</span>
            <span class="tool-name">{{ formatToolName(call.name) }}</span>
          </div>
        </div>
      </div>

      <!-- Processing indicator -->
      <div v-if="isProcessing" class="message assistant processing">
        <div class="message-header">
          <span class="role-label">AI Agent</span>
        </div>
        <div class="message-content">
          <span class="processing-dots">
            <span></span><span></span><span></span>
          </span>
          <span class="processing-text">{{ processingText }}</span>
        </div>
      </div>
    </div>

    <div class="input-area">
      <textarea
        v-model="inputText"
        @keydown.enter.exact.prevent="sendMessage"
        @keydown.shift.enter.stop
        placeholder="Describe the animation you want to create..."
        :disabled="isProcessing"
        rows="2"
        aria-label="Message input"
      ></textarea>
      <button
        class="send-btn"
        @click="sendMessage"
        :disabled="!inputText.trim() || isProcessing"
        aria-label="Send message"
      >
        <span v-if="isProcessing" class="spinner"></span>
        <span v-else>Send</span>
      </button>
    </div>

    <!-- Status bar -->
    <div class="status-bar">
      <span
        class="status-indicator"
        :class="{ connected: apiConnected, error: apiError }"
      ></span>
      <span class="status-text">{{ statusText }}</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import DOMPurify from "dompurify";
import { computed, nextTick, onMounted, ref, watch } from "vue";
import { type AIMessage, getAIAgent } from "@/services/ai";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // state
// ════════════════════════════════════════════════════════════════════════════

const selectedModel = ref<"gpt-4o" | "claude-sonnet">("gpt-4o");
const inputText = ref("");
const messages = ref<AIMessage[]>([]);
const isProcessing = ref(false);
const processingText = ref("Thinking...");
const messagesContainer = ref<HTMLElement | null>(null);
const apiConnected = ref(false);
const apiError = ref(false);

const examplePrompts = [
  "Fade in a title over 1 second",
  "Create floating particles that drift upward",
  "Make the selected layer bounce in from the left",
  "Add a glow effect to all text layers",
];

// ════════════════════════════════════════════════════════════════════════════
//                                                                  // computed
// ════════════════════════════════════════════════════════════════════════════

const statusText = computed(() => {
  if (isProcessing.value) return `Processing with ${selectedModel.value}...`;
  if (apiError.value) return "API not configured";
  if (apiConnected.value) return `Ready (${selectedModel.value})`;
  return "Checking API status...";
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // methods
// ════════════════════════════════════════════════════════════════════════════

async function checkApiStatus() {
  try {
    const response = await fetch("/lattice/api/status");
    const data = await response.json();

    if (data.status === "success") {
      apiConnected.value = data.providers.openai || data.providers.anthropic;
      apiError.value = !apiConnected.value;
    }
  } catch {
    apiConnected.value = false;
    apiError.value = true;
  }
}

async function sendMessage() {
  const text = inputText.value.trim();
  if (!text || isProcessing.value) return;

  inputText.value = "";
  isProcessing.value = true;
  processingText.value = "Thinking...";

  try {
    const agent = getAIAgent();

    // Type-safe model update using proper setter method
    const modelValue = selectedModel.value as "gpt-4o" | "claude-sonnet" | "local";
    agent.updateConfig({ model: modelValue });

    // Process instruction
    const _response = await agent.processInstruction(text);

    // Update messages from agent history
    messages.value = agent.getHistory();

    scrollToBottom();
  } catch (error) {
    const errorMessage =
      error instanceof Error ? error.message : "Unknown error";

    // Add error message
    messages.value.push({
      role: "assistant",
      content: `Error: ${errorMessage}`,
      timestamp: Date.now(),
    });
  } finally {
    isProcessing.value = false;
  }
}

function clearHistory() {
  const agent = getAIAgent();
  agent.clearHistory();
  messages.value = [];
}

function useExample(example: string) {
  inputText.value = example;
  sendMessage();
}

function formatTime(timestamp: number): string {
  const date = new Date(timestamp);
  return date.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
}

function formatContent(content: string): string {
  // Convert markdown-style formatting to HTML
  const formatted = content
    .replace(/\*\*(.*?)\*\*/g, "<strong>$1</strong>")
    .replace(/\*(.*?)\*/g, "<em>$1</em>")
    .replace(/`(.*?)`/g, "<code>$1</code>")
    .replace(/\n/g, "<br>");
  // Sanitize to prevent XSS attacks
  return DOMPurify.sanitize(formatted);
}

function formatToolName(name: string): string {
  // Convert camelCase to Title Case with spaces
  return name
    .replace(/([A-Z])/g, " $1")
    .replace(/^./, (str) => str.toUpperCase())
    .trim();
}

function getToolIcon(name: string): string {
  const icons: Record<string, string> = {
    createLayer: "+",
    deleteLayer: "-",
    duplicateLayer: "++",
    addKeyframe: "K",
    removeKeyframe: "-K",
    addEffect: "fx",
    setLayerProperty: "=",
    setLayerTransform: "T",
    configureParticles: "P",
    setTextContent: "A",
    setSplinePoints: "~",
  };
  return icons[name] || "*";
}

function scrollToBottom() {
  nextTick(() => {
    if (messagesContainer.value) {
      messagesContainer.value.scrollTop = messagesContainer.value.scrollHeight;
    }
  });
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                 // lifecycle
// ════════════════════════════════════════════════════════════════════════════

onMounted(() => {
  checkApiStatus();
});

// Auto-scroll when messages change
watch(messages, scrollToBottom, { deep: true });
</script>

<style scoped>
.ai-chat-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--surface-ground);
  color: var(--text-color);
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px 12px;
  background: var(--surface-card);
  border-bottom: 1px solid var(--surface-border);
}

.panel-title {
  font-weight: 600;
  font-size: 14px;
}

.header-actions {
  display: flex;
  gap: 8px;
  align-items: center;
}

.model-selector {
  padding: 4px 8px;
  font-size: 12px;
  background: var(--surface-ground);
  color: var(--text-color);
  border: 1px solid var(--surface-border);
  border-radius: 4px;
}

.clear-btn {
  padding: 4px 8px;
  font-size: 12px;
  background: transparent;
  color: var(--text-color-secondary);
  border: 1px solid var(--surface-border);
  border-radius: 4px;
  cursor: pointer;
}

.clear-btn:hover {
  background: var(--surface-hover);
}

.chat-messages {
  flex: 1;
  overflow-y: auto;
  padding: 12px;
}

.welcome-message {
  text-align: center;
  padding: 24px;
}

.welcome-icon {
  width: 48px;
  height: 48px;
  margin: 0 auto 12px;
  background: linear-gradient(135deg, #6366f1 0%, #8b5cf6 100%);
  border-radius: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-weight: bold;
  font-size: 18px;
  color: white;
}

.welcome-message h3 {
  margin: 0 0 8px;
  font-size: 16px;
}

.welcome-message p {
  margin: 0 0 16px;
  color: var(--text-color-secondary);
  font-size: 13px;
}

.example-prompts {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.example-btn {
  padding: 8px 12px;
  font-size: 12px;
  background: var(--surface-card);
  color: var(--text-color);
  border: 1px solid var(--surface-border);
  border-radius: 6px;
  cursor: pointer;
  text-align: left;
  transition: background 0.2s;
}

.example-btn:hover {
  background: var(--surface-hover);
  border-color: var(--primary-color);
}

.message {
  margin-bottom: 16px;
  padding: 12px;
  border-radius: 8px;
}

.message.user {
  background: var(--surface-card);
  margin-left: 24px;
}

.message.assistant {
  background: linear-gradient(135deg, rgba(99, 102, 241, 0.1) 0%, rgba(139, 92, 246, 0.1) 100%);
  margin-right: 24px;
}

.message-header {
  display: flex;
  justify-content: space-between;
  margin-bottom: 8px;
  font-size: 11px;
}

.role-label {
  font-weight: 600;
  color: var(--text-color);
}

.timestamp {
  color: var(--text-color-secondary);
}

.message-content {
  font-size: 13px;
  line-height: 1.5;
}

.message-content code {
  background: var(--surface-ground);
  padding: 2px 6px;
  border-radius: 4px;
  font-family: monospace;
  font-size: 12px;
}

.tool-calls {
  margin-top: 12px;
  padding-top: 12px;
  border-top: 1px solid var(--surface-border);
}

.tool-calls-header {
  font-size: 11px;
  color: var(--text-color-secondary);
  margin-bottom: 8px;
}

.tool-call {
  display: inline-flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  margin: 2px;
  background: var(--surface-ground);
  border-radius: 4px;
  font-size: 11px;
}

.tool-icon {
  width: 18px;
  height: 18px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--primary-color);
  color: white;
  border-radius: 4px;
  font-size: 10px;
  font-weight: bold;
}

.processing .message-content {
  display: flex;
  align-items: center;
  gap: 8px;
}

.processing-dots {
  display: flex;
  gap: 4px;
}

.processing-dots span {
  width: 6px;
  height: 6px;
  background: var(--primary-color);
  border-radius: 50%;
  animation: bounce 1.4s infinite ease-in-out both;
}

.processing-dots span:nth-child(1) { animation-delay: -0.32s; }
.processing-dots span:nth-child(2) { animation-delay: -0.16s; }
.processing-dots span:nth-child(3) { animation-delay: 0s; }

@keyframes bounce {
  0%, 80%, 100% { transform: scale(0); }
  40% { transform: scale(1); }
}

.processing-text {
  color: var(--text-color-secondary);
  font-size: 12px;
}

.input-area {
  display: flex;
  gap: 8px;
  padding: 12px;
  background: var(--surface-card);
  border-top: 1px solid var(--surface-border);
}

.input-area textarea {
  flex: 1;
  padding: 10px 12px;
  font-size: 13px;
  font-family: inherit;
  background: var(--surface-ground);
  color: var(--text-color);
  border: 1px solid var(--surface-border);
  border-radius: 8px;
  resize: none;
  outline: none;
}

.input-area textarea:focus {
  border-color: var(--primary-color);
}

.input-area textarea::placeholder {
  color: var(--text-color-secondary);
}

.send-btn {
  padding: 10px 20px;
  font-size: 13px;
  font-weight: 600;
  background: var(--primary-color);
  color: white;
  border: none;
  border-radius: 8px;
  cursor: pointer;
  transition: background 0.2s;
  min-width: 70px;
}

.send-btn:hover:not(:disabled) {
  background: var(--primary-600);
}

.send-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.spinner {
  display: inline-block;
  width: 14px;
  height: 14px;
  border: 2px solid rgba(255, 255, 255, 0.3);
  border-radius: 50%;
  border-top-color: white;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

.status-bar {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 12px;
  font-size: 11px;
  color: var(--text-color-secondary);
  background: var(--surface-ground);
  border-top: 1px solid var(--surface-border);
}

.status-indicator {
  width: 8px;
  height: 8px;
  border-radius: 50%;
  background: var(--text-color-secondary);
}

.status-indicator.connected {
  background: #22c55e;
}

.status-indicator.error {
  background: #ef4444;
}
</style>

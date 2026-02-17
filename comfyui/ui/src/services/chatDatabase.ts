/**
 * Chat Database Service
 * 
 * Provides TypeScript interface to DuckDB chat message storage.
 * Calls Haskell backend via FFI HTTP service.
 */

interface ChatMessage {
  id: string;
  project_id?: string;
  role: 'user' | 'assistant' | 'system' | 'tool';
  content: string;
  tool_calls?: unknown;
  tool_call_id?: string;
  model?: string;
  tokens_used: number;
  cost_usd: number;
  timestamp: number;
  created_at: number;
  modified_at: number;
}

interface DatabaseResponse<T> {
  status: 'success' | 'error';
  result?: T;
  message?: string;
}

const FFI_SERVICE_URL = 'http://localhost:8080';

/**
 * Save a chat message to database
 */
export async function saveChatMessage(message: ChatMessage): Promise<void> {
  const response = await fetch(`${FFI_SERVICE_URL}/ffi/save_chat_message`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      input: {
        db_path: '.lattice/database.duckdb',
        message_json: JSON.stringify(message),
      },
    }),
  });

  if (!response.ok) {
    throw new Error(`Failed to save chat message: ${response.statusText}`);
  }

  const result: DatabaseResponse<string> = await response.json();
  if (result.status === 'error') {
    throw new Error(result.message || 'Unknown error');
  }
}

/**
 * Get chat history for a project
 */
export async function getChatHistory(
  projectId?: string,
  limit: number = 100
): Promise<ChatMessage[]> {
  const response = await fetch(`${FFI_SERVICE_URL}/ffi/get_chat_history`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      input: {
        db_path: '.lattice/database.duckdb',
        project_id_json: JSON.stringify(projectId || null),
        limit,
      },
    }),
  });

  if (!response.ok) {
    throw new Error(`Failed to get chat history: ${response.statusText}`);
  }

  const result: DatabaseResponse<ChatMessage[]> = await response.json();
  if (result.status === 'error') {
    throw new Error(result.message || 'Unknown error');
  }

  return result.result || [];
}

/**
 * Search chat history using full-text search
 */
export async function searchChatHistory(
  projectId: string,
  query: string,
  limit: number = 20
): Promise<ChatMessage[]> {
  // TODO: Implement search_chat_history FFI call
  // For now, get all messages and filter client-side
  const messages = await getChatHistory(projectId, limit * 10);
  const lowerQuery = query.toLowerCase();
  return messages.filter(msg => 
    msg.content.toLowerCase().includes(lowerQuery)
  ).slice(0, limit);
}

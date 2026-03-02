#!/usr/bin/env node
/**
 * Initialize DuckDB Database
 * Creates schema and feature flags
 */

import duckdb from 'duckdb';
import { readFileSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const PROJECT_ROOT = join(__dirname, '..');
const DB_PATH = join(PROJECT_ROOT, '.lattice', 'database.duckdb');

const db = new duckdb.Database(DB_PATH);
const conn = db.connect();

console.log('Initializing DuckDB database...');

// Read and execute schema SQL
const schemaSQL = readFileSync(join(__dirname, 'init-database.sql'), 'utf-8');
conn.exec(schemaSQL, (err) => {
  if (err) {
    console.error('Error creating schema:', err);
    process.exit(1);
  }
  console.log('✅ Database schema created');

  // Read and execute feature flags SQL
  const flagsSQL = readFileSync(join(__dirname, 'init-feature-flags.sql'), 'utf-8');
  conn.exec(flagsSQL, (err) => {
    if (err) {
      console.error('Error creating feature flags:', err);
      process.exit(1);
    }
    console.log('✅ Feature flags initialized');
    
    conn.close();
    db.close();
    console.log('✅ Database initialization complete');
  });
});

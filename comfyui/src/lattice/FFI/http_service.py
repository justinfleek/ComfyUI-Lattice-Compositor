#!/usr/bin/env python3
"""
HTTP Service for Haskell FFI

Exposes Haskell FFI functions via HTTP REST API for TypeScript/JavaScript clients.

This service:
- Loads Haskell shared library via _native.py
- Exposes FFI functions as HTTP endpoints
- Handles JSON serialization/deserialization
- Provides error handling and validation

Usage:
    python http_service.py [--port 8080] [--host localhost]

Environment Variables:
    LATTICE_FFI_LIB - Path to Haskell shared library (liblattice-ffi.so)
    PORT - HTTP server port (default: 8080)
    HOST - HTTP server host (default: localhost)
"""

import json
import sys
import os
import argparse
from typing import Dict, Optional

#                                                                      // json
JSONValue = str | int | float | bool | None | list | dict
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs

# Import FFI bindings
try:
    from _native import (
        init_haskell_rts,
        call_ffi_function,
        get_available_functions,
    )
except ImportError:
    print("ERROR: Failed to import _native.py. Ensure it's in the same directory.", file=sys.stderr)
    sys.exit(1)


class FFIRequestHandler(BaseHTTPRequestHandler):
    """HTTP request handler for FFI endpoints"""
    
    def do_GET(self):
        """Handle GET requests (health check, function list)"""
        parsed_path = urlparse(self.path)
        
        if parsed_path.path == "/health":
            self.send_health_check()
        elif parsed_path.path == "/functions":
            self.send_function_list()
        else:
            self.send_error(404, "Not Found")
    
    def do_POST(self):
        """Handle POST requests (FFI function calls)"""
        parsed_path = urlparse(self.path)
        
        # Extract function name from path: /ffi/{function_name}
        path_parts = parsed_path.path.split("/")
        if len(path_parts) < 3 or path_parts[1] != "ffi":
            self.send_error(400, "Invalid path. Expected: /ffi/{function_name}")
            return
        
        function_name = path_parts[2]
        
        # Read request body
        content_length = int(self.headers.get("Content-Length", 0))
        if content_length == 0:
            self.send_error(400, "Request body required")
            return
        
        body = self.rfile.read(content_length)
        
        try:
            request_data = json.loads(body.decode("utf-8"))
            input_data = request_data.get("input")
            
            if input_data is None:
                self.send_error(400, "Missing 'input' field in request body")
                return
            
            # Call FFI function
            result = call_ffi_function(function_name, json.dumps(input_data))
            
            # Send response
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")  # CORS for development
            self.end_headers()
            self.wfile.write(result.encode("utf-8"))
            
        except json.JSONDecodeError as e:
            self.send_error(400, f"Invalid JSON: {e}")
        except Exception as e:
            self.send_error(500, f"FFI call failed: {e}")
    
    def send_health_check(self):
        """Send health check response"""
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        response = json.dumps({
            "status": "ok",
            "service": "lattice-ffi",
            "haskell_rts_initialized": True  # TODO: Check actual RTS status
        })
        self.wfile.write(response.encode("utf-8"))
    
    def send_function_list(self):
        """Send list of available FFI functions"""
        try:
            functions = get_available_functions()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            response = json.dumps({
                "status": "success",
                "functions": functions
            })
            self.wfile.write(response.encode("utf-8"))
        except Exception as e:
            self.send_error(500, f"Failed to get function list: {e}")
    
    def log_message(self, format, *args):
        """Override to use stderr for logging"""
        sys.stderr.write(f"{self.address_string()} - {format % args}\n")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="HTTP Service for Haskell FFI")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", 8080)), help="HTTP server port")
    parser.add_argument("--host", type=str, default=os.environ.get("HOST", "localhost"), help="HTTP server host")
    
    args = parser.parse_args()
    
    # Initialize Haskell RTS
    print("Initializing Haskell Runtime System...")
    if not init_haskell_rts():
        print("ERROR: Failed to initialize Haskell RTS", file=sys.stderr)
        sys.exit(1)
    
    print("Haskell RTS initialized successfully")
    
    # Create HTTP server
    server_address = (args.host, args.port)
    httpd = HTTPServer(server_address, FFIRequestHandler)
    
    print(f"Starting HTTP server on http://{args.host}:{args.port}")
    print("Endpoints:")
    print("  GET  /health - Health check")
    print("  GET  /functions - List available FFI functions")
    print("  POST /ffi/{function_name} - Call FFI function")
    print("\nPress Ctrl+C to stop")
    
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down server...")
        httpd.shutdown()


if __name__ == "__main__":
    main()

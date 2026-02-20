// HTTP server for diffusion inference
// Minimal implementation using raw sockets

#include "safetensors.hpp"
#include "tensorrt_engine.hpp"
#include "scheduler.hpp"

#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>
#include <signal.h>

#include <string>
#include <string_view>
#include <vector>
#include <unordered_map>
#include <thread>
#include <atomic>
#include <mutex>
#include <condition_variable>
#include <queue>
#include <functional>
#include <format>
#include <print>
#include <iostream>
#include <sstream>

namespace lattice {

// Simple JSON builder
class JsonBuilder {
public:
    JsonBuilder& object_start() { ss_ << '{'; first_ = true; return *this; }
    JsonBuilder& object_end() { ss_ << '}'; return *this; }
    JsonBuilder& array_start() { ss_ << '['; first_ = true; return *this; }
    JsonBuilder& array_end() { ss_ << ']'; return *this; }
    
    JsonBuilder& key(std::string_view k) {
        if (!first_) ss_ << ',';
        first_ = false;
        ss_ << '"' << k << "\":";
        return *this;
    }
    
    JsonBuilder& value(std::string_view v) {
        ss_ << '"' << v << '"';
        return *this;
    }
    
    JsonBuilder& value(int64_t v) {
        ss_ << v;
        return *this;
    }
    
    JsonBuilder& value(double v) {
        ss_ << v;
        return *this;
    }
    
    JsonBuilder& value(bool v) {
        ss_ << (v ? "true" : "false");
        return *this;
    }
    
    JsonBuilder& null_value() {
        ss_ << "null";
        return *this;
    }
    
    std::string str() const { return ss_.str(); }
    
private:
    std::ostringstream ss_;
    bool first_ = true;
};

// HTTP response
struct HttpResponse {
    int status = 200;
    std::string content_type = "application/json";
    std::string body;
    
    std::string to_string() const {
        std::ostringstream ss;
        ss << "HTTP/1.1 " << status << " ";
        switch (status) {
            case 200: ss << "OK"; break;
            case 400: ss << "Bad Request"; break;
            case 404: ss << "Not Found"; break;
            case 500: ss << "Internal Server Error"; break;
            default: ss << "Unknown"; break;
        }
        ss << "\r\n";
        ss << "Content-Type: " << content_type << "\r\n";
        ss << "Content-Length: " << body.size() << "\r\n";
        ss << "Access-Control-Allow-Origin: *\r\n";
        ss << "Connection: close\r\n";
        ss << "\r\n";
        ss << body;
        return ss.str();
    }
};

// HTTP request parser (minimal)
struct HttpRequest {
    std::string method;
    std::string path;
    std::unordered_map<std::string, std::string> headers;
    std::string body;
    
    static HttpRequest parse(std::string_view data) {
        HttpRequest req;
        
        // Find method and path
        auto line_end = data.find("\r\n");
        if (line_end == std::string_view::npos) return req;
        
        auto first_line = data.substr(0, line_end);
        auto space1 = first_line.find(' ');
        if (space1 == std::string_view::npos) return req;
        req.method = std::string(first_line.substr(0, space1));
        
        auto space2 = first_line.find(' ', space1 + 1);
        if (space2 == std::string_view::npos) return req;
        req.path = std::string(first_line.substr(space1 + 1, space2 - space1 - 1));
        
        // Find body start
        auto body_start = data.find("\r\n\r\n");
        if (body_start != std::string_view::npos) {
            req.body = std::string(data.substr(body_start + 4));
        }
        
        return req;
    }
};

// Server state
class InferenceServer {
public:
    InferenceServer(int port, const std::string& models_path)
        : port_(port), models_path_(models_path) {}
    
    void start() {
        running_ = true;
        
        // Create socket
        server_fd_ = socket(AF_INET, SOCK_STREAM, 0);
        if (server_fd_ < 0) {
            std::cerr << "Failed to create socket\n";
            return;
        }
        
        int opt = 1;
        setsockopt(server_fd_, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
        
        sockaddr_in addr{};
        addr.sin_family = AF_INET;
        addr.sin_addr.s_addr = INADDR_ANY;
        addr.sin_port = htons(port_);
        
        if (bind(server_fd_, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) < 0) {
            std::cerr << "Failed to bind to port " << port_ << "\n";
            return;
        }
        
        if (listen(server_fd_, 10) < 0) {
            std::cerr << "Failed to listen\n";
            return;
        }
        
        std::cout << "Inference server listening on port " << port_ << "\n";
        
        while (running_) {
            sockaddr_in client_addr{};
            socklen_t client_len = sizeof(client_addr);
            int client_fd = accept(server_fd_, reinterpret_cast<sockaddr*>(&client_addr), &client_len);
            
            if (client_fd < 0) continue;
            
            std::thread(&InferenceServer::handle_client, this, client_fd).detach();
        }
    }
    
    void stop() {
        running_ = false;
        if (server_fd_ >= 0) {
            close(server_fd_);
        }
    }
    
private:
    void handle_client(int client_fd) {
        char buffer[8192];
        ssize_t bytes_read = recv(client_fd, buffer, sizeof(buffer) - 1, 0);
        
        if (bytes_read <= 0) {
            close(client_fd);
            return;
        }
        
        buffer[bytes_read] = '\0';
        auto req = HttpRequest::parse(std::string_view(buffer, bytes_read));
        auto resp = route(req);
        
        auto response_str = resp.to_string();
        send(client_fd, response_str.c_str(), response_str.size(), 0);
        close(client_fd);
    }
    
    HttpResponse route(const HttpRequest& req) {
        if (req.path == "/health") {
            return handle_health();
        }
        if (req.path == "/models") {
            return handle_models();
        }
        if (req.path == "/generate/image" && req.method == "POST") {
            return handle_generate_image(req);
        }
        if (req.path == "/generate/video" && req.method == "POST") {
            return handle_generate_video(req);
        }
        if (req.path == "/generate/3d" && req.method == "POST") {
            return handle_generate_3d(req);
        }
        
        return HttpResponse{404, "application/json", R"({"error":"Not found"})"};
    }
    
    HttpResponse handle_health() {
        JsonBuilder json;
        json.object_start()
            .key("status").value("ok")
            .key("models_path").value(models_path_)
            .object_end();
        return HttpResponse{200, "application/json", json.str()};
    }
    
    HttpResponse handle_models() {
        // List available models from models_path_
        JsonBuilder json;
        json.object_start()
            .key("image_models").array_start()
                .object_start()
                    .key("id").value("flux-1-dev")
                    .key("name").value("FLUX.1 Dev")
                    .key("type").value("dit")
                    .key("params").value(int64_t{12000000000})
                .object_end()
            .array_end()
            .key("video_models").array_start()
                .object_start()
                    .key("id").value("ltx-video-13b")
                    .key("name").value("LTX-Video 13B")
                    .key("type").value("dit")
                    .key("params").value(int64_t{13000000000})
                .object_end()
                .object_start()
                    .key("id").value("hunyuan-video")
                    .key("name").value("HunyuanVideo")
                    .key("type").value("dit")
                    .key("params").value(int64_t{13000000000})
                .object_end()
                .object_start()
                    .key("id").value("wan-2.1-14b")
                    .key("name").value("Wan 2.1 T2V 14B")
                    .key("type").value("dit")
                    .key("params").value(int64_t{14000000000})
                .object_end()
            .array_end()
            .key("3d_models").array_start()
                .object_start()
                    .key("id").value("trellis-large")
                    .key("name").value("TRELLIS Large")
                    .key("type").value("dit")
                    .key("params").value(int64_t{1100000000})
                .object_end()
            .array_end()
            .object_end();
        return HttpResponse{200, "application/json", json.str()};
    }
    
    HttpResponse handle_generate_image(const HttpRequest& req) {
        // TODO: Parse request, load model, run inference
        JsonBuilder json;
        json.object_start()
            .key("status").value("pending")
            .key("message").value("Image generation not yet implemented")
            .object_end();
        return HttpResponse{200, "application/json", json.str()};
    }
    
    HttpResponse handle_generate_video(const HttpRequest& req) {
        // TODO: Parse request, load model, run inference
        JsonBuilder json;
        json.object_start()
            .key("status").value("pending")
            .key("message").value("Video generation not yet implemented")
            .object_end();
        return HttpResponse{200, "application/json", json.str()};
    }
    
    HttpResponse handle_generate_3d(const HttpRequest& req) {
        // TODO: Parse request, load model, run inference
        JsonBuilder json;
        json.object_start()
            .key("status").value("pending")
            .key("message").value("3D generation not yet implemented")
            .object_end();
        return HttpResponse{200, "application/json", json.str()};
    }
    
    int port_;
    std::string models_path_;
    int server_fd_ = -1;
    std::atomic<bool> running_{false};
};

} // namespace lattice

// Global server for signal handling
static lattice::InferenceServer* g_server = nullptr;

void signal_handler(int sig) {
    if (g_server) {
        g_server->stop();
    }
}

int main(int argc, char* argv[]) {
    int port = 8080;
    std::string models_path = "/mnt/d/models";
    
    // Parse args
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--port" && i + 1 < argc) {
            port = std::stoi(argv[++i]);
        } else if (arg == "--models" && i + 1 < argc) {
            models_path = argv[++i];
        }
    }
    
    lattice::InferenceServer server(port, models_path);
    g_server = &server;
    
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
    
    server.start();
    
    return 0;
}

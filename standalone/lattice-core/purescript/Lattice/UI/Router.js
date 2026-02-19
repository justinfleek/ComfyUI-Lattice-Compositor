// Router.js - Browser History API FFI

export const getPathname = () => window.location.pathname;

export const pushState = (path) => () => {
  window.history.pushState({}, "", path);
  // Dispatch popstate so listeners pick it up
  window.dispatchEvent(new PopStateEvent("popstate"));
};

export const replaceState = (path) => () => {
  window.history.replaceState({}, "", path);
};

export const onPopState = (callback) => () => {
  window.addEventListener("popstate", () => {
    callback(window.location.pathname)();
  });
};

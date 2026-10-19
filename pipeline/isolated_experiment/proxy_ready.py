"""Add only model-service attachment hosts observed during connectivity tests."""
import runpy

namespace = runpy.run_path("/base-proxy.py")
namespace["ALLOWED"].update({
    "sdmntprindiasocentral.oaiusercontent.com",
    "sdmntprsouthcentralus.oaiusercontent.com",
    "sdmntprcentralus.oaiusercontent.com",
})
with namespace["Server"](("0.0.0.0", 3128), namespace["Handler"]) as server:
    server.serve_forever()

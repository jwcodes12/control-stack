"""R2 public collector entry point: Docker daemon observations, no attestation."""
from tools.collect_deployment_docker import capture, normalize
__all__=['capture','normalize']

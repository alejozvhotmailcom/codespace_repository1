"""
Lanzador: descarga / consulta masiva de historias clínicas (Vie Cloud IndiGO + plantillas).
"""
from __future__ import annotations

import os
import sys
from pathlib import Path


def main() -> None:
    if getattr(sys, "frozen", False):
        os.chdir(Path(sys.executable).resolve().parent)
    import indigo_historias_core  # noqa: E402

    indigo_historias_core.indigo_historias_main()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nInterrumpido por el usuario.")
        sys.exit(130)
    except SystemExit as e:
        raise e
    except Exception as e:
        print(f"\nERROR: {e}", file=sys.stderr)
        import traceback

        traceback.print_exc()
        if getattr(sys, "frozen", False):
            try:
                input("\nPulse Enter para cerrar…")
            except EOFError:
                pass
        sys.exit(1)

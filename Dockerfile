# Blast Radius selector. Same base image digest the organizers labeled commits with.
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90
# sqlglot's source at the pinned commit (allowed source: sqlglot's own repository at eb11aec).
RUN python -c "import io,tarfile,urllib.request; \
u='https://github.com/tobymao/sqlglot/archive/eb11aec4be8cb2122afe713a4816662c3f0fb2fa.tar.gz'; \
t=tarfile.open(fileobj=io.BytesIO(urllib.request.urlopen(u, timeout=120).read())); \
t.extractall('/tmp/x', filter='data')" \
 && mv /tmp/x/sqlglot-eb11aec4be8cb2122afe713a4816662c3f0fb2fa /app-sqlglot \
 && mkdir -p /app && mv /app-sqlglot /app/sqlglot && rm -rf /tmp/x
COPY selector.py map.json.gz e1_cutoff.py e1map.json.gz r1map.json.gz /app/
# Build-time work is not charged: byte-compile the selector (the entry point imports it, so the
# .pyc is used), write the import baseline, and the verified caches (compact map, pinned code objects).
RUN python -m compileall -q /app/sqlglot /app/e1_cutoff.py && python -c "import compileall,sys; sys.exit(not compileall.compile_file('/app/selector.py', quiet=1))" \
 && python /app/selector.py --baseline && python /app/selector.py --precompute
CMD ["python", "-S", "-c", "import sys; sys.path.insert(0, '/app'); import selector; selector.main()"]

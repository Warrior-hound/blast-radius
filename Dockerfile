FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90
RUN python -c "import io,tarfile,urllib.request; \
u='https://github.com/tobymao/sqlglot/archive/eb11aec4be8cb2122afe713a4816662c3f0fb2fa.tar.gz'; \
t=tarfile.open(fileobj=io.BytesIO(urllib.request.urlopen(u, timeout=120).read())); \
t.extractall('/tmp/x', filter='data')" \
 && mv /tmp/x/sqlglot-eb11aec4be8cb2122afe713a4816662c3f0fb2fa /app-sqlglot \
 && mkdir -p /app && mv /app-sqlglot /app/sqlglot && rm -rf /tmp/x
RUN pip install --no-cache-dir --target /app/vdeps duckdb==2.0.0 pandas==3.1.1 numpy==2.5.5 pytz==2026.6     python-dateutil==4.0.0 tzdata==2026.6 setuptools==84.2.1 setuptools-scm==10.3.4
COPY prof.py selector.py map.json.gz e1_cutoff.py e1map.json.gz r1map.json.gz e2_ns.py e2map.json.gz fixture_openers.json verify.py vserve.py vtests.json order_state.py /app/
RUN python -m compileall -q /app/sqlglot /app/e1_cutoff.py /app/verify.py /app/vserve.py && python -c "import compileall,sys; sys.exit(not compileall.compile_file('/app/selector.py', quiet=1))" \
 && python /app/selector.py --baseline && python /app/selector.py --precompute \
 && mkdir -p /app/cache && PYTHONHASHSEED=0 python -I -S /app/e2_ns.py build /app/sqlglot /app/cache/e2fp.pickle /app/cache/e2fp.canon.json \
 && python /app/order_state.py build /app/sqlglot /app/map.json.gz /app/cache/order_state.json /app/e2map.json.gz \
 && python -S /app/vserve.py measure /app/vtests.json /app/cache/vcost.json && rm -rf /tmp/rwxv
ENV RWX_E2=1
CMD ["python", "-S", "-c", "import sys; sys.path.insert(0, '/app'); import selector; selector.main()"]

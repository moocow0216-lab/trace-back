#!/usr/bin/env bash
# 合約量化進場：雲端主機一鍵安裝（Ubuntu 22.04 / 24.04，用 root 執行）
# 用法：把 quant-server.js 和這個檔案放在同一個資料夾，執行  sudo bash setup.sh
set -euo pipefail

APP_DIR=/opt/quant
PORT=8787
cd "$(dirname "$0")"

if [ "$(id -u)" -ne 0 ]; then echo "請用 root 執行：sudo bash setup.sh"; exit 1; fi
if [ ! -f quant-server.js ]; then echo "找不到 quant-server.js，請把它和 setup.sh 放在同一個資料夾"; exit 1; fi

echo "== 1/6 檢查這台主機能不能連到幣安 =="
code=$(curl -s -o /dev/null -w '%{http_code}' https://fapi.binance.com/fapi/v1/ping || true)
if [ "$code" != "200" ]; then
  echo "!! 連不到幣安合約 API（HTTP $code）。幣安會擋美國等地區的 IP。"
  echo "!! 請把主機換到日本、新加坡或香港等地區後再執行一次。"
  exit 1
fi
echo "幣安連線正常"

# 記憶體小於 2GB（例如 512MB 方案）時，加 1GB 備用記憶體，避免回測時記憶體不夠而當掉
if [ "$(free -m | awk '/^Mem:/{print $2}')" -lt 2000 ] && ! swapon --show | grep -q /swapfile; then
  echo "== 建立 1GB 備用記憶體（swap）=="
  fallocate -l 1G /swapfile || dd if=/dev/zero of=/swapfile bs=1M count=1024
  chmod 600 /swapfile && mkswap /swapfile && swapon /swapfile
  grep -q '^/swapfile' /etc/fstab || echo '/swapfile none swap sw 0 0' >> /etc/fstab
fi

echo "== 2/6 安裝 Node.js 20 =="
apt-get update -y
apt-get install -y curl ca-certificates gnupg debian-keyring debian-archive-keyring apt-transport-https openssl
if ! command -v node >/dev/null || [ "$(node -p 'process.versions.node.split(".")[0]')" -lt 18 ]; then
  curl -fsSL https://deb.nodesource.com/setup_20.x | bash -
  apt-get install -y nodejs
fi
node -v

echo "== 3/6 安裝 Caddy（自動申請 HTTPS 憑證）=="
if ! command -v caddy >/dev/null; then
  curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/gpg.key' | gpg --dearmor -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
  curl -1sLf 'https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt' > /etc/apt/sources.list.d/caddy-stable.list
  apt-get update -y
  apt-get install -y caddy
fi

echo "== 4/6 安裝伺服器程式 =="
id -u quant >/dev/null 2>&1 || useradd --system --home "$APP_DIR" --shell /usr/sbin/nologin quant
mkdir -p "$APP_DIR/data"
cp quant-server.js "$APP_DIR/"
if [ ! -f "$APP_DIR/.env" ]; then
  echo "ADMIN_KEY=$(openssl rand -hex 16)" > "$APP_DIR/.env"
  echo "PORT=$PORT" >> "$APP_DIR/.env"
fi
chown -R quant:quant "$APP_DIR"
chmod 600 "$APP_DIR/.env"

cat > /etc/systemd/system/quant.service <<EOF
[Unit]
Description=Quant scanner server
After=network-online.target
Wants=network-online.target

[Service]
User=quant
WorkingDirectory=$APP_DIR
EnvironmentFile=$APP_DIR/.env
ExecStart=/usr/bin/node $APP_DIR/quant-server.js
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
EOF
systemctl daemon-reload
systemctl enable --now quant
systemctl restart quant

echo "== 5/6 設定 HTTPS 網址 =="
IP=$(curl -4 -s https://api.ipify.org || curl -4 -s https://ifconfig.me)
DOMAIN=${DOMAIN:-"${IP//./-}.sslip.io"}
cat > /etc/caddy/Caddyfile <<EOF
$DOMAIN {
  encode gzip
  reverse_proxy 127.0.0.1:$PORT
}
EOF
systemctl reload caddy || systemctl restart caddy
if command -v ufw >/dev/null && ufw status | grep -q active; then ufw allow 80,443/tcp; fi

echo "== 6/6 檢查 =="
sleep 3
curl -s "http://127.0.0.1:$PORT/api/ping" && echo
KEY=$(grep ADMIN_KEY "$APP_DIR/.env" | cut -d= -f2)
echo
echo "================ 完成 ================"
echo "伺服器網址：https://$DOMAIN"
echo "管理金鑰：  $KEY"
echo "（第一次申請 HTTPS 憑證可能要等 1～2 分鐘）"
echo "請把這兩個填進網頁「合約量化進場 → ☁ 雲端伺服器」。管理金鑰不要給別人。"
echo "看執行紀錄：journalctl -u quant -f"

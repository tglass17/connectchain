# ConnectChain
Needs a Node server (WebSockets) — GitHub Pages alone can't run it.
1. Push this folder to GitHub.
2. Deploy on Render/Railway/Fly (Web Service, build `npm install`, start `npm start`).
3. Set env var `OWNER_PASSWORD` to your secret password. Log in as `guynamedtucker` with it.
Note: free hosts wipe `data.json` on redeploy — use a persistent disk or a database for permanent accounts.

# Configuration file for News Bot
# Contains API keys, thresholds and settings

import os
from dotenv import load_dotenv

load_dotenv()

# Bybit API Configuration
BYBIT_API_KEY = os.getenv("BYBIT_API_KEY", "")
BYBIT_API_SECRET = os.getenv("BYBIT_API_SECRET", "")
BYBIT_TESTNET = os.getenv("BYBIT_TESTNET", "false").lower() == "true"

# Telegram Notification Configuration
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")

# News Sources Configuration
NEWS_SOURCES = {
    "cryptocompare": "https://min-api.cryptocompare.com/data/v2/news",
    "coingecko": "https://api.coingecko.com/api/v3/news",
    "cointelegraph": "https://api.cointelegraph.com/v3/news",
}

# Impact Threshold (0-10 scale, notifications sent if impact >= threshold)
IMPACT_THRESHOLD = 3

# Scanning intervals
SCAN_INTERVAL_SECONDS = 300  # Check news every 5 minutes
CACHE_DURATION_HOURS = 24    # Keep processed news for 24 hours

# Keywords that indicate market-moving news
HIGH_IMPACT_KEYWORDS = [
    "listing", "partnership", "adoption", "regulation", "hack",
    "security breach", "merger", "acquisition", "presale",
    "mainnet", "upgrade", "airdrop", "burned", "tokenomics",
]

MEDIUM_IMPACT_KEYWORDS = [
    "update", "announcement", "community", "development",
    "roadmap", "team", "integration", "milestone",
]

# Coins to monitor on Bybit
MONITORED_COINS = [
    "BTC", "ETH", "SOL", "XRP", "ADA", "DOGE", "LINK",
    "POLKA", "AVAX", "MATIC", "ATOM", "ARB", "NEAR", "OP",
]

# Logging configuration
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")
LOG_FILE = "bot.log"

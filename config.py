# Configuration file for News Bot
# Contains API keys, thresholds and settings

import os
from dotenv import load_dotenv
import requests

load_dotenv()

# Bybit API Configuration
BYBIT_API_KEY = os.getenv("BYBIT_API_KEY", "")
BYBIT_API_SECRET = os.getenv("BYBIT_API_SECRET", "")
BYBIT_TESTNET = os.getenv("BYBIT_TESTNET", "false").lower() == "true"
BYBIT_BASE_URL = "https://api.bybit.com"
BYBIT_FUTURES_URL = f"{BYBIT_BASE_URL}/v5/market"

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

# Logging configuration
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")
LOG_FILE = "bot.log"


def get_bybit_futures_coins():
    """
    Fetch all available futures trading pairs from Bybit
    Returns list of coin symbols (e.g., ['BTC', 'ETH', 'SOL', ...])
    """
    try:
        url = f"{BYBIT_FUTURES_URL}/tickers?category=linear"
        response = requests.get(url, timeout=10)
        response.raise_for_status()
        data = response.json()
        
        coins = set()
        
        if data.get("result") and data["result"].get("list"):
            for item in data["result"]["list"]:
                symbol = item.get("symbol", "")
                # Extract coin symbol from trading pair (e.g., "BTCUSDT" -> "BTC")
                if symbol.endswith("USDT"):
                    coin = symbol.replace("USDT", "")
                    coins.add(coin)
        
        return sorted(list(coins))
    except Exception as e:
        print(f"Error fetching Bybit futures coins: {e}")
        # Fallback to default list if API fails
        return [
            "BTC", "ETH", "SOL", "XRP", "ADA", "DOGE", "LINK",
            "POLKA", "AVAX", "MATIC", "ATOM", "ARB", "NEAR", "OP",
            "APE", "BLUR", "INJ", "MEME", "PEPE", "SHIB", "DYDX",
            "SEI", "SUI", "APT", "FET", "AIOZ", "AI", "WIF",
        ]


# Dynamically load all Bybit futures coins
MONITORED_COINS = get_bybit_futures_coins()

print(f"✅ Loaded {len(MONITORED_COINS)} coins from Bybit futures")
print(f"Monitoring: {', '.join(MONITORED_COINS[:20])}{'...' if len(MONITORED_COINS) > 20 else ''}")

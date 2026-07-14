# Bybit Futures Manager
# Manages interaction with Bybit API for futures trading pairs

import requests
import logging
from typing import List, Dict, Optional
from datetime import datetime
from config import BYBIT_BASE_URL, BYBIT_API_KEY, BYBIT_API_SECRET, LOG_FILE, LOG_LEVEL

# Setup logging
logging.basicConfig(
    level=LOG_LEVEL,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILE),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)


class BybitManager:
    """Manages Bybit futures data and trading pairs"""

    def __init__(self):
        self.base_url = BYBIT_BASE_URL
        self.api_key = BYBIT_API_KEY
        self.api_secret = BYBIT_API_SECRET
        self.cached_coins = None
        self.cache_time = None

    def get_all_futures_coins(self, use_cache: bool = True) -> List[str]:
        """
        Get all available futures trading pairs from Bybit
        Returns list of coin symbols
        """
        try:
            url = f"{self.base_url}/v5/market/tickers?category=linear"
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

            coins_list = sorted(list(coins))
            logger.info(f"Fetched {len(coins_list)} futures coins from Bybit")
            
            self.cached_coins = coins_list
            self.cache_time = datetime.now()
            
            return coins_list

        except Exception as e:
            logger.error(f"Error fetching Bybit futures coins: {e}")
            # Return cached list if available
            if self.cached_coins:
                logger.info(f"Using cached list of {len(self.cached_coins)} coins")
                return self.cached_coins
            return []

    def get_futures_ticker(self, symbol: str) -> Optional[Dict]:
        """
        Get futures ticker data for a specific coin
        Returns dict with price, change, volume, etc.
        """
        try:
            url = f"{self.base_url}/v5/market/tickers?category=linear&symbol={symbol}USDT"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            data = response.json()

            if data.get("result") and data["result"].get("list"):
                item = data["result"]["list"][0]
                return {
                    "symbol": symbol,
                    "price": float(item.get("lastPrice", 0)),
                    "price_change_24h": float(item.get("price24hPcnt", 0)) * 100,
                    "high_24h": float(item.get("highPrice24h", 0)),
                    "low_24h": float(item.get("lowPrice24h", 0)),
                    "volume_24h": float(item.get("volume24h", 0)),
                    "turnover_24h": float(item.get("turnover24h", 0)),
                    "bid": float(item.get("bid1Price", 0)),
                    "ask": float(item.get("ask1Price", 0)),
                    "timestamp": datetime.now().isoformat(),
                }
            return None

        except Exception as e:
            logger.error(f"Error fetching ticker for {symbol}: {e}")
            return None

    def get_multiple_tickers(self, coins: List[str]) -> List[Dict]:
        """Get ticker data for multiple coins"""
        tickers = []
        for coin in coins:
            ticker = self.get_futures_ticker(coin)
            if ticker:
                tickers.append(ticker)
        return tickers

    def get_futures_open_interest(self, symbol: str) -> Optional[Dict]:
        """
        Get open interest data for a futures pair
        Useful for understanding market positions
        """
        try:
            url = f"{self.base_url}/v5/market/open-interest?category=linear&symbol={symbol}USDT&intervalTime=5min"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            data = response.json()

            if data.get("result") and data["result"].get("list"):
                item = data["result"]["list"][0]
                return {
                    "symbol": symbol,
                    "open_interest": float(item.get("openInterest", 0)),
                    "timestamp": item.get("timestamp"),
                }
            return None

        except Exception as e:
            logger.error(f"Error fetching open interest for {symbol}: {e}")
            return None

    def get_funding_rate(self, symbol: str) -> Optional[Dict]:
        """
        Get current funding rate for a futures pair
        High funding rate can indicate strong trend
        """
        try:
            url = f"{self.base_url}/v5/market/funding/history?category=linear&symbol={symbol}USDT&limit=1"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            data = response.json()

            if data.get("result") and data["result"].get("list"):
                item = data["result"]["list"][0]
                return {
                    "symbol": symbol,
                    "funding_rate": float(item.get("fundingRate", 0)) * 100,  # Convert to percentage
                    "funding_timestamp": item.get("fundingRateTimestamp"),
                }
            return None

        except Exception as e:
            logger.error(f"Error fetching funding rate for {symbol}: {e}")
            return None

    def is_coin_tradeable(self, symbol: str) -> bool:
        """Check if a coin has active futures trading pair on Bybit"""
        try:
            ticker = self.get_futures_ticker(symbol)
            return ticker is not None
        except Exception as e:
            logger.error(f"Error checking if {symbol} is tradeable: {e}")
            return False

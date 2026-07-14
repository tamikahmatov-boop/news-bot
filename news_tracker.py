# News Tracker Module
# Monitors news from various sources and analyzes impact on coins

import requests
import logging
from datetime import datetime, timedelta
from typing import List, Dict, Optional
import json
from config import (
    NEWS_SOURCES, HIGH_IMPACT_KEYWORDS, MEDIUM_IMPACT_KEYWORDS,
    CACHE_DURATION_HOURS, MONITORED_COINS, LOG_FILE, LOG_LEVEL
)

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


class NewsTracker:
    """Tracks crypto news and analyzes impact on coins"""

    def __init__(self):
        self.processed_news = {}
        self.last_check = {}

    def fetch_coingecko_news(self) -> List[Dict]:
        """Fetch news from CoinGecko API"""
        try:
            url = NEWS_SOURCES["coingecko"]
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            data = response.json()

            news_list = []
            for item in data.get("data", [])[:50]:  # Get last 50 news
                news_list.append({
                    "title": item.get("title", ""),
                    "description": item.get("description", ""),
                    "source": item.get("source", ""),
                    "url": item.get("url", ""),
                    "published_at": item.get("published_at", ""),
                    "image_url": item.get("image_url", ""),
                })
            logger.info(f"Fetched {len(news_list)} news from CoinGecko")
            return news_list
        except Exception as e:
            logger.error(f"Error fetching CoinGecko news: {e}")
            return []

    def fetch_cryptocompare_news(self, coin: str) -> List[Dict]:
        """Fetch news for specific coin from CryptoCompare"""
        try:
            url = f"{NEWS_SOURCES['cryptocompare']}?categories={coin}&sortOrder=latest"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            data = response.json()

            news_list = []
            for item in data.get("Data", [])[:30]:
                news_list.append({
                    "title": item.get("title", ""),
                    "description": item.get("body", ""),
                    "source": item.get("source", ""),
                    "url": item.get("url", ""),
                    "published_at": item.get("published_at", ""),
                })
            logger.info(f"Fetched {len(news_list)} news for {coin} from CryptoCompare")
            return news_list
        except Exception as e:
            logger.error(f"Error fetching CryptoCompare news for {coin}: {e}")
            return []

    def calculate_impact_score(self, title: str, description: str) -> int:
        """
        Calculate impact score (0-10) for news based on keywords
        Higher score = higher market impact potential
        """
        text = (title + " " + description).lower()
        impact_score = 0

        # Check for high-impact keywords
        for keyword in HIGH_IMPACT_KEYWORDS:
            if keyword.lower() in text:
                impact_score += 3

        # Check for medium-impact keywords
        for keyword in MEDIUM_IMPACT_KEYWORDS:
            if keyword.lower() in text:
                impact_score += 1

        # Negative keywords reduce impact
        negative_keywords = ["rumor", "speculation", "alleged", "might", "could"]
        for keyword in negative_keywords:
            if keyword.lower() in text:
                impact_score = max(0, impact_score - 1)

        # Cap at 10
        impact_score = min(10, impact_score)

        return impact_score

    def extract_mentioned_coins(self, text: str) -> List[str]:
        """Extract coin names mentioned in the news"""
        mentioned = []
        text_upper = text.upper()

        for coin in MONITORED_COINS:
            if coin in text_upper:
                mentioned.append(coin)

        return list(set(mentioned))  # Remove duplicates

    def is_news_relevant(self, title: str, description: str) -> bool:
        """Check if news is relevant to monitored coins"""
        text = (title + " " + description).lower()

        # Check if any monitored coin is mentioned
        for coin in MONITORED_COINS:
            if coin.lower() in text:
                return True

        # Check for general crypto news that affects all coins
        general_keywords = [
            "bitcoin", "ethereum", "crypto", "blockchain",
            "sec", "regulation", "fed", "interest rate",
            "bull market", "bear market", "crash", "rally"
        ]
        for keyword in general_keywords:
            if keyword in text:
                return True

        return False

    def process_news(self, coin: str) -> List[Dict]:
        """
        Process and filter news for a specific coin
        Returns list of news with impact scores
        """
        all_news = []

        # Fetch from multiple sources
        coingecko_news = self.fetch_coingecko_news()
        cryptocompare_news = self.fetch_cryptocompare_news(coin)

        all_news.extend(coingecko_news)
        all_news.extend(cryptocompare_news)

        processed_results = []

        for news_item in all_news:
            title = news_item.get("title", "")
            description = news_item.get("description", "")
            news_id = hash(title)  # Simple ID generation

            # Skip if already processed
            if news_id in self.processed_news:
                continue

            # Check relevance
            if not self.is_news_relevant(title, description):
                continue

            # Calculate impact
            impact_score = self.calculate_impact_score(title, description)

            # Check mentioned coins
            mentioned_coins = self.extract_mentioned_coins(title + " " + description)

            result = {
                "id": news_id,
                "coin": coin,
                "title": title,
                "description": description,
                "impact_score": impact_score,
                "mentioned_coins": mentioned_coins,
                "source": news_item.get("source", "Unknown"),
                "url": news_item.get("url", ""),
                "timestamp": datetime.now().isoformat(),
            }

            processed_results.append(result)
            self.processed_news[news_id] = datetime.now()

            logger.info(f"Processed news for {coin}: {title[:50]}... (Impact: {impact_score}/10)")

        # Clean old cache
        self._clean_old_cache()

        return processed_results

    def _clean_old_cache(self):
        """Remove old news from cache"""
        cutoff_time = datetime.now() - timedelta(hours=CACHE_DURATION_HOURS)
        old_ids = [
            news_id for news_id, timestamp in self.processed_news.items()
            if timestamp < cutoff_time
        ]
        for news_id in old_ids:
            del self.processed_news[news_id]

        if old_ids:
            logger.info(f"Cleaned {len(old_ids)} old news from cache")

    def get_monitored_coins(self) -> List[str]:
        """Return list of monitored coins"""
        return MONITORED_COINS.copy()

# Main Bot Module
# Orchestrates news tracking and Telegram notifications

import asyncio
import logging
from datetime import datetime
from typing import List, Dict
import requests
from news_tracker import NewsTracker
from config import (
    TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID, IMPACT_THRESHOLD,
    SCAN_INTERVAL_SECONDS, MONITORED_COINS, LOG_FILE, LOG_LEVEL
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


class NewsBot:
    """Main bot that tracks news and sends notifications"""

    def __init__(self):
        self.tracker = NewsTracker()
        self.is_running = False
        self.sent_notifications = set()

    def _format_impact_bar(self, score: int) -> str:
        """Create visual impact bar (0-10 scale)"""
        filled = int(score)
        empty = 10 - filled
        bar = "█" * filled + "░" * empty
        return bar

    def _create_notification_message(self, news_item: Dict) -> str:
        """Format news item into Telegram message"""
        impact_bar = self._format_impact_bar(news_item["impact_score"])

        message = (
            f"📰 <b>НОВОСТЬ О {news_item['coin']}</b>\n\n"
            f"<b>Заголовок:</b> {news_item['title']}\n\n"
            f"<b>Описание:</b> {news_item['description'][:200]}...\n\n"
            f"<b>Уровень влияния на манету:</b>\n"
            f"{impact_bar} {news_item['impact_score']}/10\n\n"
        )

        if news_item["mentioned_coins"]:
            message += f"<b>Упомянутые токены:</b> {', '.join(news_item['mentioned_coins'])}\n\n"

        message += (
            f"<b>Источник:</b> {news_item['source']}\n"
            f"<b>Время:</b> {news_item['timestamp'][:19]}\n\n"
            f"🔗 <a href='{news_item['url']}'>Читать полностью</a>"
        )

        return message

    def send_telegram_notification(self, message: str) -> bool:
        """Send notification to Telegram"""
        if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
            logger.warning("Telegram credentials not configured")
            return False

        try:
            url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
            payload = {
                "chat_id": TELEGRAM_CHAT_ID,
                "text": message,
                "parse_mode": "HTML",
                "disable_web_page_preview": False,
            }

            response = requests.post(url, json=payload, timeout=10)
            response.raise_for_status()

            logger.info(f"Notification sent to Telegram")
            return True

        except Exception as e:
            logger.error(f"Error sending Telegram notification: {e}")
            return False

    def process_news_batch(self, coins: List[str]) -> List[Dict]:
        """Process news for a batch of coins"""
        all_news = []

        for coin in coins:
            try:
                news_items = self.tracker.process_news(coin)
                all_news.extend(news_items)
            except Exception as e:
                logger.error(f"Error processing news for {coin}: {e}")

        return all_news

    def filter_by_impact_threshold(self, news_items: List[Dict]) -> List[Dict]:
        """Filter news by impact threshold"""
        filtered = [
            item for item in news_items
            if item["impact_score"] >= IMPACT_THRESHOLD
        ]
        logger.info(f"Filtered {len(news_items)} news items, {len(filtered)} meet threshold")
        return filtered

    def notify_significant_news(self, news_items: List[Dict]):
        """Send notifications for significant news"""
        for news_item in news_items:
            # Create unique ID for this news to avoid duplicate notifications
            news_id = (news_item["id"], news_item["coin"])

            if news_id in self.sent_notifications:
                continue

            # Create and send message
            message = self._create_notification_message(news_item)
            success = self.send_telegram_notification(message)

            if success:
                self.sent_notifications.add(news_id)
                logger.info(f"Notification sent for: {news_item['title'][:50]}")
            else:
                logger.warning(f"Failed to send notification for: {news_item['title'][:50]}")

    async def scan_news(self):
        """Scan news for all monitored coins"""
        logger.info("Starting news scan...")

        # Process news for all monitored coins
        all_news = self.process_news_batch(MONITORED_COINS)
        logger.info(f"Total news items found: {len(all_news)}")

        # Filter by impact threshold
        significant_news = self.filter_by_impact_threshold(all_news)
        logger.info(f"Significant news items: {len(significant_news)}")

        # Send notifications
        if significant_news:
            self.notify_significant_news(significant_news)

        logger.info("News scan completed")

    async def run(self):
        """Main bot loop"""
        logger.info("=" * 50)
        logger.info("NEWS BOT STARTED")
        logger.info(f"Monitoring coins: {', '.join(MONITORED_COINS)}")
        logger.info(f"Impact threshold: {IMPACT_THRESHOLD}/10")
        logger.info(f"Scan interval: {SCAN_INTERVAL_SECONDS} seconds")
        logger.info("=" * 50)

        self.is_running = True

        try:
            while self.is_running:
                try:
                    await self.scan_news()
                except Exception as e:
                    logger.error(f"Error in main loop: {e}")

                # Wait before next scan
                logger.info(f"Next scan in {SCAN_INTERVAL_SECONDS} seconds...")
                await asyncio.sleep(SCAN_INTERVAL_SECONDS)

        except KeyboardInterrupt:
            logger.info("Bot interrupted by user")
            self.is_running = False
        except Exception as e:
            logger.error(f"Unexpected error: {e}")
            self.is_running = False

    def stop(self):
        """Stop the bot"""
        self.is_running = False
        logger.info("Bot stopped")


def main():
    """Entry point"""
    bot = NewsBot()

    try:
        asyncio.run(bot.run())
    except KeyboardInterrupt:
        logger.info("Shutting down...")
        bot.stop()


if __name__ == "__main__":
    main()

WITH cost_by_month AS (
    SELECT
        campaign_id AS campaign,
        DATE_TRUNC('month', created_date) AS month,
        SUM(cost) AS monthly_cost
    FROM
        marketing
    WHERE
        created_date BETWEEN
            NOW() - INTERVAL '3 months' AND
            NOW()
    GROUP BY
        campaign_id,
        DATE_TRUNC('month', created_date)
)
SELECT
    campaign,
    AVG(monthly_cost) as avg_monthly_cost
FROM cost_by_month
GROUP BY campaign
ORDER BY campaign;


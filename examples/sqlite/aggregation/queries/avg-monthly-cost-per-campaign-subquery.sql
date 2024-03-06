SELECT
    campaign,
    AVG(monthly_cost) as avg_monthly_cost
FROM (
    SELECT
        campaign_id AS campaign,
        STRFTIME('%Y-%m', created_date, 'unixepoch') AS month,
        SUM(cost) AS monthly_cost
    FROM
        marketing
    WHERE
        DATE(created_date, 'unixepoch') BETWEEN
            DATE(DATE(), '-3 months') AND
            DATE()
    GROUP BY
        campaign_id,
        STRFTIME('%Y-%m', created_date, 'unixepoch')
)
GROUP BY campaign
ORDER BY campaign;


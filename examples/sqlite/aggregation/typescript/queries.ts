/*
 * Code generated by sqlgen. DO NOT EDIT.
 */

export interface Dispatcher {
    (query: string, args?: unknown[]): Promise<{
        keys: string[];
        rows: unknown[][];
    }>;
}

function mapRows<TResult>(keys: string[], rows: unknown[][]): TResult[] {
    const out = Array(rows.length)
    for (let i = 0; i < out.length; i++) {
        const row = rows[i];
        out[i] = Object.fromEntries(pairs(keys, row));
    }
    return out as TResult[];
}

function pairs<T, U>(xs: T[], ys: U[]): [T, U][] {
    const out = Array(xs.length)
    for (let i = 0; i < out.length; i++) {
        out[i] = [xs[i], ys[i]];
    }
    return out;
}

export type AvgMonthlyCostPerCampaignCteResult = {
    campaign: number;
    avgMonthlyCost: number;
};

export async function avgMonthlyCostPerCampaignCte(
    dispatch: Dispatcher,
): Promise<AvgMonthlyCostPerCampaignCteResult[]> {
    const query = `
        WITH cost_by_month AS (
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
        SELECT
            campaign,
            AVG(monthly_cost) as avg_monthly_cost
        FROM cost_by_month
        GROUP BY campaign
        ORDER BY campaign;
    `;

    const result = await dispatch(query);
    return mapRows<AvgMonthlyCostPerCampaignCteResult>(result.keys, result.rows);
}

export type AvgMonthlyCostPerCampaignSubqueryResult = {
    campaign: number;
    avgMonthlyCost: number;
};

export async function avgMonthlyCostPerCampaignSubquery(
    dispatch: Dispatcher,
): Promise<AvgMonthlyCostPerCampaignSubqueryResult[]> {
    const query = `
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
    `;

    const result = await dispatch(query);
    return mapRows<AvgMonthlyCostPerCampaignSubqueryResult>(result.keys, result.rows);
}


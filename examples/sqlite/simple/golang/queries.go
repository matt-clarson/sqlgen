// Code generated by sqlgen. DO NOT EDIT.

package queries

import (
	"context"
	"database/sql"
)

type CountTable1Result struct {
	NumRows int32
}

func CountTable1(db *sql.DB, ctx context.Context) ([]CountTable1Result, error) {
	query := `
        SELECT
            count(*) AS num_rows
        FROM table_1;
    `

	rows, err := db.QueryContext(ctx, query)
	if err != nil {
		return nil, err
	}

	var results []CountTable1Result

	for rows.Next() {
		r := CountTable1Result{}
		err := rows.Scan(
			&r.NumRows,
		)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}

	return results, rows.Err()
}

type GetJoinedResult struct {
	T1Id       int32
	ColA       sql.NullString
	ColB       string
	T2Id       int32
	SomeValue  sql.NullFloat64
	OtherValue []byte
}

func GetJoined(db *sql.DB, ctx context.Context) ([]GetJoinedResult, error) {
	query := `
        SELECT 
            t1.id t1_id,
            col_a,
            col_b,
            t2.id t2_id,
            some_value,
            other_value
        FROM
            table_1 t1
            JOIN table_2 t2 ON
                t1.id=t2.ref_1
            JOIN table_3 t3 ON
                t1.id=t3.ref_1
        ORDER BY t1.id
        LIMIT 10;
    `

	rows, err := db.QueryContext(ctx, query)
	if err != nil {
		return nil, err
	}

	var results []GetJoinedResult

	for rows.Next() {
		r := GetJoinedResult{}
		err := rows.Scan(
			&r.T1Id,
			&r.ColA,
			&r.ColB,
			&r.T2Id,
			&r.SomeValue,
			&r.OtherValue,
		)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}

	return results, rows.Err()
}

type GetTable1Result struct {
	Id   int32
	ColA sql.NullString
	ColB string
}

func GetTable1(db *sql.DB, ctx context.Context) ([]GetTable1Result, error) {
	query := `
        SELECT * FROM table_1;
    `

	rows, err := db.QueryContext(ctx, query)
	if err != nil {
		return nil, err
	}

	var results []GetTable1Result

	for rows.Next() {
		r := GetTable1Result{}
		err := rows.Scan(
			&r.Id,
			&r.ColA,
			&r.ColB,
		)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}

	return results, rows.Err()
}

type InsertTable1Arg struct {
	Id   int32
	ColA sql.NullString
	ColB string
}

func InsertTable1(db *sql.DB, ctx context.Context, arg InsertTable1Arg) error {
	query := `
        INSERT INTO table_1
        VALUES (
            ?,
            ?,
            ?
        );
    `

	_, err := db.ExecContext(ctx, query,
		arg.Id,
		arg.ColA,
		arg.ColB,
	)

	return err
}

type QueryJoinedArg struct {
	Msg string
	Val float64
}

type QueryJoinedResult struct {
	T1Id      int32
	ColA      sql.NullString
	SomeValue sql.NullFloat64
}

func QueryJoined(db *sql.DB, ctx context.Context, arg QueryJoinedArg) ([]QueryJoinedResult, error) {
	query := `
        SELECT
            t1.id t1_id,
            col_a,
            some_value
        FROM
            table_1 t1
            JOIN table_2 t2
                ON t1.id=t2.ref_1
        WHERE
            col_b = ? AND
            some_value > ?;
    `

	rows, err := db.QueryContext(ctx, query,
		arg.Msg,
		arg.Val,
	)
	if err != nil {
		return nil, err
	}

	var results []QueryJoinedResult

	for rows.Next() {
		r := QueryJoinedResult{}
		err := rows.Scan(
			&r.T1Id,
			&r.ColA,
			&r.SomeValue,
		)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}

	return results, rows.Err()
}


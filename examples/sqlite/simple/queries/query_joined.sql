SELECT
    t1.id t1_id,
    col_a,
    some_value
FROM
    table_1 t1
    JOIN table_2 t2
        ON t1.id=t2.ref_1
WHERE
    col_b = $msg::text AND
    some_value > $val::float;

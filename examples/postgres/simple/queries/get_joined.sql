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


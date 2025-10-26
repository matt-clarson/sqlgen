INSERT INTO table_1
VALUES (
    $id::int,
    $col_a::?text,
    $col_b::text
) ON CONFLICT DO
    UPDATE
    SET col_a=$col_a,
        col_b=$col_b;


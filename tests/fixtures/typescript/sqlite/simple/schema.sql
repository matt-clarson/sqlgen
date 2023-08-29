CREATE TABLE table_1 (
    id INT PRIMARY KEY,
    col_a TEXT,
    col_b TEXT NOT NULL
);

CREATE TABLE table_2 (
    id INT PRIMARY KEY,
    ref_1 INT NOT NULL,
    FOREIGN KEY(ref_1) REFERENCES table_1(id)
);

CREATE TABLE table_3 (
    id INT PRIMARY KEY,
    ref_1 INT,
    FOREIGN KEY(ref_1) REFERENCES table_1(id)
);

CREATE TABLE table_1 (
    id INT PRIMARY KEY,
    col_a TEXT,
    col_b TEXT NOT NULL
);

CREATE TABLE table_2 (
    id INT PRIMARY KEY,
    ref_1 INT NOT NULL,
    some_value FLOAT,
    FOREIGN KEY(ref_1) REFERENCES table_1(id)
);

CREATE TABLE table_3 (
    id INT PRIMARY KEY,
    ref_1 INT,
    other_value BLOB,
    FOREIGN KEY(ref_1) REFERENCES table_1(id)
);

CREATE TABLE table_4 (
    id UUID PRIMARY KEY,
    created TIMESTAMP WITH TIME ZONE NOT NULL,
    updated TIMESTAMP WITH TIME ZONE
);

CREATE TABLE table_5 (
    id INT PRIMARY KEY,
    words TEXT[]
);

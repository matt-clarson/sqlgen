CREATE TABLE users (
    id INT PRIMARY KEY,
    email TEXT NOT NULL UNIQUE,
    created INT NOT NULL
);

CREATE TABLE items (
    id INT PRIMARY KEY,
    name TEXT NOT NULL
);

CREATE TABLE user_items (
    user INT NOT NULL,
    item INT NOT NULL,
    PRIMARY KEY (user, item),
    FOREIGN KEY (user) REFERENCES users(id),
    FOREIGN KEY (item) REFERENCES items(id)
);

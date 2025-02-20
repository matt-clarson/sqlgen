ALTER TABLE users
DROP COLUMN first_name;

ALTER TABLE users
DROP COLUMN last_name;

ALTER TABLE users
RENAME COLUMN nickname TO username;

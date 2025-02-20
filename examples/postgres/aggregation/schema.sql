CREATE TABLE campaign (
    id INT PRIMARY KEY,
    details TEXT NOT NULL
);

CREATE TABLE marketing (
    id INT PRIMARY KEY,
    campaign_id INT NOT NULL REFERENCES campaign(id),
    cost INT NOT NULL,
    created_date TIMESTAMP NOT NULL
);

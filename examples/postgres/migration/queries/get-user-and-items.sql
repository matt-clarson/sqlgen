SELECT
    u.username,
    i.name,
    i.rating
FROM
    users u
        LEFT JOIN user_items ui ON u.id=ui.user
        LEFT JOIN items i ON ui.item=i.id
WHERE
    u.email = $email::text;

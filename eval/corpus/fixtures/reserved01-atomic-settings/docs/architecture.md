transactions.py owns validation and atomicity. cli.py owns transport and exit status. No operation may mutate the supplied settings object.

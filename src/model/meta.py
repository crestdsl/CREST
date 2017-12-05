PARENT_IDENTIFIER = "_parent"
CURRENT_IDENTIFIER = "current"
NAME_IDENTIFIER = "_name"

class CrestObject(object):
    def __init__(self, name="", parent=None):
        setattr(self, NAME_IDENTIFIER, name)
        setattr(self, PARENT_IDENTIFIER, parent)

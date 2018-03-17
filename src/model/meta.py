PARENT_IDENTIFIER = "_parent"
CURRENT_IDENTIFIER = "current"
NAME_IDENTIFIER = "_name"


class CrestObject(object):
    def __init__(self, name="", parent=None):
        setattr(self, NAME_IDENTIFIER, name)
        setattr(self, PARENT_IDENTIFIER, parent)


class crestlist(list):
    """ a special class that's produced when using an annotation with several states (transitions, updates)"""
    @staticmethod
    def fromlist(listt):
        new = crestlist()
        new.extend(listt)
        return new

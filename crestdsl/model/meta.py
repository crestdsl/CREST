PARENT_IDENTIFIER = "_parent"
CURRENT_IDENTIFIER = "current"
NAME_IDENTIFIER = "_name"
DEPENDENCY_IDENTIFIER = "_dependencies"

import crestdsl.model.api as api

class CrestObject(object):
    def __init__(self, name="", parent=None):
        setattr(self, NAME_IDENTIFIER, name)
        setattr(self, PARENT_IDENTIFIER, parent)

    def __str__(self):
        texts = [api.get_name(self)]
        parent = api.get_parent(self)

        while parent is not None and api.get_name(parent) is not "":
            texts.insert(0, api.get_name(parent))
            parent = api.get_parent(parent)
        else:
            if api.get_name(self) is None or api.get_name(self) is "":
                texts = [self.__class__.__name__]
            else:
                texts.insert(0, parent.__class__.__name__)
        # print(texts)
        return ".".join(texts)


class CrestList(list):
    """ a special class that's produced when using an annotation with several states (transitions, updates)"""
    @staticmethod
    def fromlist(listt):
        new = CrestList()
        new.extend(listt)
        return new

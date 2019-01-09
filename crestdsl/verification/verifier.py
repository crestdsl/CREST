

# def badstate(source="")
#     def decorator(state)

class Verifier(object):

    def __init__(self, system):
        self.model = system

    def check_bad_reachable(self):
        return False

import unittest
from crestdsl.simulation.epsilon import Epsilon, eps

class EpsilonTest(unittest.TestCase):

    def test_eps_basic(self):
        self.assertEqual(Epsilon(epsilon=1), eps)
        self.assertEqual(Epsilon(epsilon=1)-Epsilon(epsilon=1), eps-eps)
        self.assertEqual(Epsilon(epsilon=1)-Epsilon(epsilon=1), 0)
        self.assertEqual(eps, eps)

    def test_eps_comparisons(self):
        self.assertLess(0, eps)
        self.assertLess(eps, 0.000000001)
        self.assertLess(eps, 0.1)
        self.assertLess(eps, 1)

        self.assertLessEqual(0, eps)
        self.assertLessEqual(eps, 0.000000001)
        self.assertLessEqual(eps, 0.1)
        self.assertLessEqual(eps, 1)

        self.assertGreater(eps, 0)
        self.assertGreater(0.00000000001, eps)
        self.assertGreater(0.1, eps)
        self.assertGreater(1, eps)

        self.assertGreaterEqual(eps, 0)
        self.assertGreaterEqual(0.00000000001, eps)
        self.assertGreaterEqual(0.1, eps)
        self.assertGreaterEqual(1, eps)

        self.assertLess(eps + eps + eps, eps + eps + eps + eps)
        self.assertLessEqual(eps + eps + eps, eps + eps + eps)


        self.assertEqual(min(1, 2+eps, 3-eps, 1-eps, 1+eps), 1-eps)
        self.assertEqual(max(1, -2+eps, -3-eps, 1-eps, 1+eps), 1+eps)

    def test_eps_math(self):

        self.assertEqual(Epsilon(-1, 1), eps-1)
        self.assertEqual(Epsilon(1, -1), 1-eps)

        self.assertEqual(Epsilon(2, -1), 2 - eps)

        self.assertEqual(Epsilon(2, 1), 2 + eps)
        self.assertEqual(Epsilon(2, -1), 2 - eps)
        self.assertEqual(Epsilon(5, -2), 5 - eps - eps)
        self.assertEqual(Epsilon(3, 2), 3 + eps + eps)

        self.assertEqual(Epsilon(2, 1) + 2, 4 + eps)
        self.assertEqual(Epsilon(2, 1) + Epsilon(2, 1), 4 + eps + eps)

        self.assertEqual(Epsilon(2, 1) - 2, eps)
        self.assertEqual(Epsilon(2, 1) - Epsilon(2, 1), 0)

        self.assertEqual(Epsilon(2, 1) - 2, eps)
        self.assertEqual(Epsilon(2, 1) - Epsilon(2, 1), 0)


        self.assertEqual(-Epsilon(2, 1), Epsilon(-2, -1))
        self.assertEqual(-Epsilon(2, -1), Epsilon(-2, 1))
        self.assertEqual(-Epsilon(), Epsilon())

        self.assertEqual(30 - (25 + eps), 5 - eps)


    def test_eps_str(self):
        self.assertEqual(str(eps), "\u03B5")
        self.assertEqual(str(-eps), "-\u03B5")
        self.assertEqual(str(Epsilon(2,1)), "2 + \u03B5")
        self.assertEqual(str(Epsilon(3,-1)), "3 - \u03B5")
        self.assertEqual(str(Epsilon(2,2)), "2 + 2 * \u03B5")
        self.assertEqual(str(Epsilon(3,-3)), "3 - 3 * \u03B5")

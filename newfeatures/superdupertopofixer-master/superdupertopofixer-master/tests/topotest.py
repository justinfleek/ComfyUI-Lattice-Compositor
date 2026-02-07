import unittest
import tempfile
import random
import string
import os


class TopoTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp_dir_obj = tempfile.TemporaryDirectory()
        cls.tmp_dir_name = cls.tmp_dir_obj.name

    @classmethod
    def build_config(cls, **kwargs):
        tmp_file_name = str.join(
            "", [random.choice(string.ascii_letters) for _ in range(15)]
        )
        tmp_path = os.path.join(cls.tmp_dir_name, tmp_file_name)
        with open(tmp_path, "w") as f:
            for key in kwargs:
                print(key, kwargs[key], file=f)
        return tmp_path


if __name__ == "__main__":
    print("To test the topofixer use the test files in the directory.")

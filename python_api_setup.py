#!/usr/bin/env python

import os, sys
import argparse
import subprocess
from distutils.core import setup, Extension

p = argparse.ArgumentParser()
p.add_argument('--msat-lib-dir', required=True)
p.add_argument('--msat-include-dir', required=True)
p.add_argument('--swig-tool', required=True)
p.add_argument('--build-dir', required=True)

opts = p.parse_args()

sys.argv = [sys.argv[0]] + [ 'build_ext', '--inplace', '--build-temp',
                             opts.build_dir, '--force']

if subprocess.call([opts.swig_tool, '-I'+ opts.msat_include_dir,
                    '-I' + os.path.dirname(__file__),
                    '-python', '-o', 'ic3ia_python_wrap.c',
                    os.path.join(os.path.dirname(__file__),
                                 'ic3ia_python.i')]) == 0:
    setup(name='ic3ia', version='0.1',
          ext_modules=[Extension('_ic3ia', ['ic3ia_python_wrap.c'],
                                 include_dirs=[opts.msat_include_dir,
                                               os.path.dirname(__file__)],
                                 library_dirs=[opts.build_dir,
                                               opts.msat_lib_dir],
                                 libraries=['ic3ia', 'mathsat', 'gmpxx', 'gmp'],
                                 language='c++',
                                 )]
          )

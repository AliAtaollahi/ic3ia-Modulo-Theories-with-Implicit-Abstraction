/* -*- swig -*- */

%include "typemaps.i"

%typemap(in) const char **options {
    int i, sz;
    char **tmp;
    if (!PySequence_Check($input)) {
        PyErr_SetString(PyExc_TypeError, "Sequence object required");
        return NULL;
    }
    sz = PySequence_Size($input);
    tmp = malloc(sizeof(const char *) * (sz+1));
    for (i = 0; i < sz; ++i) {
        PyObject *p = PySequence_ITEM($input, i);
        char *s = PyString_AsString(p);
        Py_DECREF(p);
        if (s == NULL) {
            free(tmp);
            return NULL;
        } else {
            tmp[i] = s;
        }
    }
    tmp[sz] = NULL;
    $1 = tmp;
}
%typemap(freearg) const char **options {
    if ($1) free($1);
}


%ignore ic3ia_create_from_file;
%ignore ic3ia_set_search_bound_callback;
%rename(_ic3ia_create) ic3ia_create; 

%module ic3ia
%{
#include "ic3ia.h"
%}

%include "ic3ia.h"

%{

%}

%inline %{
#undef IC3IA_ERROR
static int IC3IA_ERROR(ic3ia_solver s) { return s.repr == NULL; }
%}

%pythoncode %{

import sys

if sys.version_info[0] >= 3:
    def _enc(s):
        if isinstance(s, str): s = s.encode('ascii')
        return s
else:                         
    def _enc(s): return s


def ic3ia_create(vmt, opts):
    opts = [_enc(o) for o in opts]
    return _ic3ia_create(vmt, opts)

%}

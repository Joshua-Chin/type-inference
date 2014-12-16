from functools import namedtuple

EConst = namedtuple('EConst', 'val')
EVar = namedtuple('EVar', 'name')
EAbs = namedtuple('EAbs', ['arg', 'body'])
EApp = namedtuple('EApp', ['func', 'arg'])
ELet = namedtuple('ELet', ['var', 'val', 'body'])

TBase = namedtuple('TBase', 'name')
TVar = namedtuple('TVar', 'name')
TFunc = namedtuple('TFunc', ['arg', 'result'])

TScheme = namedtuple('TScheme', ['bound_types', 'type'])

TInt = TBase('TInt')
TBool = TBase('TBool')

def substitute(substitution, type_):
    if isinstance(type_, TBase):
        return type_
    if isinstance(type_, TVar):
        if type_ in substitution:
            return substitution[type_]
        return type_
    if isinstance(type_, TFunc):
        return TFunc(substitute(substitution, type_.arg),
                     substitute(substitution, type_.result))
    if isinstance(type_, TScheme):
        new_subs = {find:replace for find,replace in substition.items()
                    if find not in type_.bound_types}
        return TScheme(type_.bound_types, substitute(new_subs, type_.type))
    if isinstance(type_, dict):
        return {expr: substitute(substitution, val)
                for expr, val in type_.items()}
    
def unify(t1, t2):
    if isinstance(t1, TBase) and isinstance(t2, TBase):
        if t1 == t2:
            return {}
    if isinstance(t1, TVar):
        return {t1: t2}
    if isinstance(t2, TVar):
        return {t2: t1}
    if isinstance(t1, TFunc) and isinstance(t2, TFunc):
        s1 = unify(t1.arg, t2.arg)
        s2 = unify(substitute(s1, t1.result), substitute(s1, t2.result))
        s1.update(s2)
        return s1
        
    raise TypeError

var_index = 0
def newvar():
    global var_index
    result = TVar(var_index)
    var_index += 1
    return result

def instantiate(type_scheme):
    if isinstance(type_scheme, TScheme):
        subs = {type_: newvar() for type_ in type_scheme.bound_types}
        return substitute(subs, type_scheme.type)
    return type_scheme

def generalize(environment, type_):
    return TScheme(free_vars(type_), type_)

def free_vars(type_):
    if isinstance(type_, TBase):
        return set()
    if isinstance(type_, TVar):
        return {type_}
    if isinstance(type_, TFunc):
        return free_vars(type_.result) | free_vars(type_.arg)
    if isinstance(type_, TScheme):
        return free_vars(type_.type) - type_.bound_types
    if isinstance(type_, dict):
        result = set()
        for x in type_.values():
            result |= free_vars(x)
        return result

def inference_type(expr, env=None):
    if env is None:
        env = {}
    s, t = w(env, expr)
    return s, generalize(env, t)

def w(env, expr):
    if isinstance(expr, EVar):
        if expr in env:
            return ({}, instantiate(env[expr]))
    if isinstance(expr, EAbs):
        u = newvar()
        new_env = dict(env)
        new_env[expr.arg] = u
        s1, t1 = w(new_env, expr.body)
        return (s1, TFunc(substitute(s1, u), t1))
    if isinstance(expr, EApp):
        s1, t1 = w(env, expr.func)
        s2, t2 = w(substitute(s1, env), expr.arg)
        u = newvar()
        s3 = unify(substitute(s2, t1), TFunc(t2, u))
        s1.update(s2)
        s1.update(s3)
        return (s1, substitute(s3, u))
    if isinstance(expr, ELet):
        u = newvar()
        new_env = dict(env)
        new_env[expr.var] = u
        s1, t1 = w(new_env, expr.val)
        s2 = unify(t1, substitute(s1, u))
        s2t1 = substitute(s2, t1)
        s1.update(s2)
        new_env = substitute(s1, env)
        v = generalize(new_env, s2t1)
        new_env[expr.var] = v
        s3, t2 = w(new_env, expr.body)
        s1.update(s3)
        return (s1, t2)
        
    raise TypeError
    


def test_unify():
    print(unify(TFunc(TInt, TInt), TFunc(TVar('foo'), TVar('bar'))))
    print(unify(TFunc(TInt, TVar('foo')), TFunc(TVar('foo'), TVar('bar'))))

def test_instantiate():
    print(instantiate(TScheme([TVar('foo')], TFunc(TVar('foo'), TInt))))

def test_free_vars():
    print(free_vars(TScheme({TVar('foo')}, TVar('foo'))))

def test_inference_type():
    print(inference_type(EAbs(EVar('foo'), EVar('foo'))))
    print(inference_type(ELet(EVar('id'), EAbs(EVar('foo'), EVar('foo')), EVar('id'))))
    print(inference_type(EAbs(EVar('foo'), EAbs(EVar('bar'), EApp(EVar('foo'), EVar('bar'))))))
    
if __name__ == '__main__':
    test_inference_type()

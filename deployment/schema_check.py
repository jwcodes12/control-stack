"""Dependency-free validator for the explicit JSON Schema subset used here.
Unknown schema keywords and external references fail; no schema is downloaded.
"""
import math
import re

class UnsupportedSchema(ValueError):pass

def validate(value,schema,root=None,path='$'):
    root=schema if root is None else root
    allowed={'$schema','$id','$defs','$ref','title','description','type','properties','required','additionalProperties','items','minItems','maxItems','minLength','pattern','minimum','maximum','enum','const','anyOf','oneOf','allOf'}
    if not isinstance(schema,dict) or set(schema)-allowed:raise UnsupportedSchema(path+': unsupported schema keyword or schema shape')
    def need(ok,message):
        if not ok:raise ValueError(path+': '+message)
    if '$ref' in schema:
        reference=schema['$ref']
        if not isinstance(reference,str) or not reference.startswith('#/'):raise UnsupportedSchema(path+': external schema reference unsupported')
        target=root
        for part in reference[2:].split('/'):target=target[part.replace('~1','/').replace('~0','~')]
        validate(value,target,root,path)
    for key in ('anyOf','oneOf'):
        if key in schema:
            count=0
            for branch in schema[key]:
                try:validate(value,branch,root,path);count+=1
                except UnsupportedSchema:raise
                except ValueError:pass
            need(count==1 if key=='oneOf' else count>=1,key+' branches do not match')
    for branch in schema.get('allOf',[]):validate(value,branch,root,path)
    types={'object':isinstance(value,dict),'array':isinstance(value,list),'string':isinstance(value,str),'boolean':type(value) is bool,'integer':type(value) is int,'number':type(value) is int or type(value) is float and math.isfinite(value),'null':value is None}
    if 'type' in schema:
        choices=schema['type'] if isinstance(schema['type'],list) else [schema['type']]
        need(all(t in types for t in choices),'unsupported type');need(any(types[t] for t in choices),'wrong value type')
    if 'const' in schema:need(type(value) is type(schema['const']) and value==schema['const'],'wrong constant')
    if 'enum' in schema:need(any(type(value) is type(candidate) and value==candidate for candidate in schema['enum']),'not in enum')
    if isinstance(value,dict):
        need(all(key in value for key in schema.get('required',[])),'missing required field')
        properties=schema.get('properties',{})
        for key,item in value.items():
            child=properties.get(key,schema.get('additionalProperties',True))
            need(child is not False,'extra field '+key)
            if isinstance(child,dict):validate(item,child,root,path+'.'+key)
    if isinstance(value,list):
        need(len(value)>=schema.get('minItems',0),'too few items');need(len(value)<=schema.get('maxItems',len(value)),'too many items')
        if 'items' in schema:
            for index,item in enumerate(value):validate(item,schema['items'],root,path+'['+str(index)+']')
    if isinstance(value,str):
        need(len(value)>=schema.get('minLength',0),'string too short')
        if 'pattern' in schema:need(re.search(schema['pattern'],value) is not None,'pattern mismatch')
    if type(value) in (int,float):
        need(type(value) is int or math.isfinite(value),'non-finite JSON number')
        if 'minimum' in schema:need(value>=schema['minimum'],'below minimum')
        if 'maximum' in schema:need(value<=schema['maximum'],'above maximum')
    return value

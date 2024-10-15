#!/usr/bin/python

import linecache

set_logic = '(set-logic QF_AUFBV)\n'
arg = "xarg"
bbfunc_name = "xisalpha"
bmc_k = 1

search_string=bbfunc_name + '@' + arg 
print('search string: ' + search_string)

bbfun_declaration = []
bbfun_applications = []

a_file = open("out.smt2", "r")
list_of_lines = a_file.readlines()
fileslice = 0

for line in list_of_lines:
    fileslice = fileslice + 1
    if 'Encoding to solver time' in line:
        break;
        
list_of_lines = list_of_lines[fileslice:]


for line_no, line in enumerate(list_of_lines):
    if search_string in line:
        if 'assert' in line:
            bbfun_applications.append((line_no, line))
        if 'declare' in line:
            bbfun_declaration.append((line_no, line))


line_replacements = {}
# TODO: arg type should be taken from the smtlib declaration itself
argname_list = []

for tup in bbfun_applications:
    # function call is split in two lines make them
    # a single line in tempstr
    nxtline =  list_of_lines[tup[0]+1] 
    tempstr = (tup[1].rstrip('\n') + nxtline)
    wordlist = tempstr.split(' ')
    retstr = ''
    argname = ''
    for word in wordlist:
        if 'return' in word:
            retstr = word.split('))')[0]
        elif 'xarg' in word:
            argname = word.split(')')[0]
            
    replstr = '(assert (= (' + bbfunc_name + ' ' + argname + ') ' + retstr  + '))\n'
    list_of_lines[tup[0]] = replstr
    list_of_lines[tup[0]+1] = '\n';


# adding declrations
decl_stmt = '(declare-fun xisalpha ((_ BitVec 8)) (_ BitVec 32))\n'
list_of_lines.insert(0, decl_stmt)
list_of_lines.insert(0, set_logic)

# removing "\\" generated during smt dump
for id in xrange(len(list_of_lines)):
    list_of_lines[id] = list_of_lines[id].replace("\\","")

list_of_lines.append('(check-sat)\n')
    

n_file = open("proc.smt2", "w")
n_file.writelines(list_of_lines)
n_file.close()

a_file.close()



    
    

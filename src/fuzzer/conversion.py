prefix = """#include "aufbv-evaluator.h"
#include "assert.h"
#include "llvm/Support/raw_ostream.h"

namespace cvc5 {
namespace cgen {

float bv2float(uint64_t bv) {
  uint32_t fbv = bv;
  float f;
  memcpy(&f, &fbv, sizeof(float));
  return f;
}

double bv2double(uint64_t bv) {
  uint64_t dbv = bv;
  double d;
  memcpy(&d, &dbv, sizeof(double));
  return d;
}

uint64_t float2bv(float f) {
  uint32_t fbv;
  memcpy(&fbv, &f, sizeof(float));
  return fbv;
}

uint64_t double2bv(double d) {
  uint64_t dbv;
  memcpy(&dbv, &d, sizeof(double));
  return dbv;
}

uint64_t evaluateExFunc(void* func, std::vector<unsigned int> widthVector, std::vector<bool> isFloatVector, std::vector<uint64_t> args){
  assert(func != nullptr);
  unsigned int argc = args.size();
  unsigned int ret_width = widthVector[0];
  bool ret_isfloat = isFloatVector[0];
  // FIXME: function pointer type may be buggy
  uint64_t v = 0;
"""
suffix = """
  assert(false);
}
}
}
"""
def main():
    MAX_ARGC = 8
    types = ["uint8_t", "uint16_t", "uint32_t", "uint64_t"]
    widths_map = {
        "uint8_t": 8,
        "uint16_t": 16,
        "uint32_t": 32,
        "uint64_t": 64,
        "float": 32,
        "double": 64
    }
    code = []
    code.append(prefix)
    for i in range(0, MAX_ARGC + 1):
        indent = 2
        code.append(" " *  indent + "if (argc == %d) {" % i)
        indent += 2
        for ret_type in ["uint8_t", "uint16_t", "uint32_t", "uint64_t", "float", "double"]:
            cases = len(types) ** i
            for j in range(cases):
                arg_type_list = []
                ignore = False
                for k in range(i):
                    l = types[(j // (len(types) ** (i - 1 - k))) % len(types)]
                    if 'float' not in types and 'double' not in types:
                        if i == 4 and l in ["uint8_t"]:
                            ignore = True
                            break
                        if i >= 5 and i <= 8 and l in ["uint8_t", "uint16_t"]:
                            ignore = True
                            break
                        if i > 8:
                            assert False, "Too many arguments: {}".format(MAX_ARGC)
                    else:
                        if i == 3 and l in ["uint8_t", "float"]:
                            ignore = True
                            break
                        if i == 4 and l in ["uint8_t", "uint16_t", "float"]:
                            ignore = True
                            break
                        if i >= 5 and i <= 8 and l in ["uint8_t", "uint16_t", "uint32_t", "float"]:
                            ignore = True
                            break
                        if i > 8:
                            assert False, "Too many arguments: {}".format(MAX_ARGC)
                    arg_type_list.append(l)
                if ignore:
                    continue
                func_type = "(({}(*)({}))func)".format(ret_type, ", ".join(arg_type_list))
                args_list = []
                for k in range(i):
                    if arg_type_list[k] == "float":
                        args_list.append("bv2float(args[{}])".format(k))
                    elif arg_type_list[k] == "double":
                        args_list.append("bv2double(args[{}])".format(k))
                    else:
                        args_list.append("args[{}]".format(k))
                func_call = "v = " + func_type + "(" + ", ".join(args_list) + ");"
                if i == 0:
                    if ret_type == "float":
                        condition = "if (ret_isfloat && ret_width == 32)"
                    elif ret_type == "double":
                        condition = "if (ret_isfloat && ret_width == 64)"
                    else:
                        condition = "if (!ret_isfloat && ret_width == {})".format(widths_map[ret_type])
                else:
                    if ret_type == "float":
                        condition = "if (ret_isfloat && ret_width == 32 && "
                    elif ret_type == "double":
                        condition = "if (ret_isfloat && ret_width == 64 && "
                    else:
                        condition = "if (!ret_isfloat && ret_width == {} && ".format(widths_map[ret_type])
                    args_list = []
                    for k in range(i):
                        if arg_type_list[k] == "float":
                            args_list.append("isFloatVector[{}] && widthVector[{}] == 32".format(k+1, k+1))
                        elif arg_type_list[k] == "double":
                            args_list.append("isFloatVector[{}] && widthVector[{}] == 64".format(k+1, k+1))
                        else:
                            args_list.append("!isFloatVector[{}] && widthVector[{}] == {}".format(k+1, k+1, widths_map[arg_type_list[k]]))
                    condition = condition + " && ".join(args_list) + ")"
                code.append(" " *  indent + condition + " {")
                indent += 2
                code.append(" " *  indent + func_call)
                if ret_type == "float":
                    code.append(" " *  indent + "return float2bv(v);")
                elif ret_type == "double":
                    code.append(" " *  indent + "return double2bv(v);")
                else:
                    code.append(" " *  indent + "return v;")
                indent -= 2
                code.append(" " *  indent + "}")
        if 'float' not in types and 'double' not in types:
            tail_func_type = "(({}(*)({}))func)".format(ret_type, ", ".join(["uint64_t"] * i))
            code.append(" " *  indent + "v = " + tail_func_type + "(" + ", ".join(["args[{}]".format(k) for k in range(i)]) + ");")
            code.append(" " *  indent + "return v;")
        else:
            code.append(" " *  indent + "assert(false);")
        indent -= 2
        code.append(" " *  indent + "}")
    code.append(suffix)
    print('\n'.join(code))
if __name__ == "__main__":
    main()
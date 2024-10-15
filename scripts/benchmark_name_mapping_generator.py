import os
import sys

def benchmark_name_mapping_generator(benchmark_dir):
    template_path = "./benchmark_name_mapping_template.csv"
    output_path = "./benchmark_name_mapping.csv"
    if not os.path.exists(template_path):
        print("Template file not found!")
        return
    with open(template_path, "r") as template_file:
        template_content = template_file.read()
        template_content = template_content.replace("$TEST_DIR", benchmark_dir)
        with open(output_path, "w") as output_file:
            output_file.write(template_content)
        print("Benchmark name mapping file generated successfully!")

if __name__ == '__main__':
    assert len(sys.argv) == 2
    benchmark_dir = sys.argv[1]
    if not os.path.exists(benchmark_dir):
        print("Benchmark directory not found!")
        sys.exit(1)
    benchmark_name_mapping_generator(benchmark_dir)
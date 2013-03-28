#!/usr/bin/python
from __future__ import with_statement
import os, sys, re

def get_times(file_name):
    with open(file_name, 'r') as f:
        lines = f.readlines()
    lines = [re.sub('coqc.*?\\s([^\\s]+)$', r'coqc \1', i.replace('\n', '').strip())
             for i in lines
             if i[:4] in ('coqc', 'real')]
    times_dict = {}
    for i in range(len(lines) - 1):
        if lines[i][:4] == 'coqc':
            if lines[i + 1][:4] == 'real':
                name = lines[i][4:].strip()
                time = lines[i + 1][4:].strip()
                minutes, seconds = time.split('m')
                if seconds[0].isdigit() and seconds[1] == '.':
                    # we want,e.g., 0m05.111s, not 0m5.111s
                    seconds = '0' + seconds
                time = '%sm%s' % (minutes, seconds)
                times_dict[name] = time
    return times_dict
            
def get_sorted_file_list_from_times_dict(times_dict, descending=True):
    def get_key(name):
        minutes, seconds = times_dict[name].replace('s', '').split('m')
        return (int(minutes), float(seconds))
    return sorted(times_dict.keys(), key=get_key, reverse=descending)

def make_table_string(left_times_dict, right_times_dict,
                      descending=True,
                      left_tag="After", right_tag="Before"):
    names = get_sorted_file_list_from_times_dict(left_times_dict, descending=descending)
    left_width = max(map(len, left_times_dict.values()))
    right_width = max(map(len, right_times_dict.values()))
    middle_width = max(map(len, names + ["File Name"]))
    format_string = "%%-%ds | %%-%ds | %%-%ds" % (left_width, middle_width, right_width)
    header = format_string % (left_tag, "File Name", right_tag)
    sep = '-' * len(header)
    return '\n'.join([header, sep] + [format_string % (left_times_dict[name],
                                                       name,
                                                       right_times_dict[name])
                                      for name in names])

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print('Usage: %s LEFT_FILE_NAME RIGHT_FILE_NAME [OUTPUT_FILE_NAME]')
        sys.exit(1)
    else:
        left_dict = get_times(sys.argv[1])
        right_dict = get_times(sys.argv[2])
        table = make_table_string(left_dict, right_dict)
        if len(sys.argv) == 3 or sys.argv[3] == '-':
            print(table)
        else:
            with open(sys.argv[3], 'w') as f:
                f.write(table)

            

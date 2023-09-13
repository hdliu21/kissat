import re

#Open the log file
interested_list = []
with open("test.log", "r") as file:
    # Read each line in the file
    for line in file:
        # Check if the line contains the string "Propagating literals"
        if "Propagating literals" in line:
            # Use regular expression to find the numbers on the line
            matches = re.findall(r"-?\d+", line)
            # Extract and print the numbers
            if matches:
                numbers = [int(match) for match in matches]
                interested_list += numbers
                # print("Numbers found on the line:", numbers)
print(len(interested_list))
count_dict = {}
for element in interested_list:
    # Use dict.get() to get the current count of the element (defaulting to 0 if the element is not yet in the dictionary)
    count = count_dict.get(abs(element), 0)
    # Increment the count by 1
    count += 1
    # Update the count for the element in the dictionary
    count_dict[abs(element)] = count

print(count_dict)
print(len(count_dict))
sorted_items = sorted(count_dict.items(), key=lambda x: x[0])
cnt = 0
tmp = []
for key, value in sorted_items:
    cnt += value
    tmp.append(value)
    print(f"Key: {key}, Value: {value}")
print(cnt)

print("int myArray[] = {", end="")
print(", ".join(str(value) for value in tmp), end="")
print("};")



# interested_list = []
# with open("test.log", "r") as file:
#     # Read each line in the file
#     for line in file:
#         # Check if the line contains the string "Propagating literals"
#         if "propagated number is" in line:
#             # Use regular expression to find the numbers on the line
#             matches = re.findall(r"-?\d+", line)
#             # Extract and print the numbers
#             if matches:
#                 numbers = [int(match) for match in matches]
#                 interested_list += numbers
#                 # print("Numbers found on the line:", numbers)
# print(sum(interested_list))
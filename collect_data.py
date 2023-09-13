# Open the file in read mode
file = open("dump.log", "r")

# Create a dictionary to store the lines and their counts
lines = {}
cnt  = 0
# Loop through each line in the file
for line in file:
  # Strip the newline character and the prefix "reducible clause: "
  if line.startswith("redundant clause: "):
    cnt += 1
  else:
    continue
  line = line.strip().replace("redundant clause: ", "")
  # Check if the line is already in the dictionary
  if line in lines:
    # Increment the count by one
    lines[line] += 1
  else:
    # Add the line to the dictionary with count one
    lines[line] = 1

# Close the file
file.close()

# Loop through the dictionary items
more_than_2 = 0
equals_2 = 0
for line, count in lines.items():
  # Print the line and its count if it is more than one
  if count > 1:
    print(line, "(", count, ")")
    more_than_2 += 1
  if count == 2:
    equals_2 += 1
  # else:
  #   print(line)
print(len(lines))
print(cnt)
print(more_than_2)
print(equals_2)

import json

# 读取JSON文件
with open('e-humantime/humantime/humantime.json', 'r') as f:
    data = json.load(f)

# 获取targets字典
targets = data.get('targets', {})

# 统计符合条件的键的数量
count = 0
for key in targets.keys():
    if key.startswith('<') and ' as ' in key and '>::' in key:
        count += 1

print(f"符合条件的target数量: {count}")
print(f"总target数量: {len(targets)}")
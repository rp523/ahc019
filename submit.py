from pathlib import Path
import time

def get_min_score() -> float:
    tgt_dir_path = Path("../ahc019_optuna")
    csv_path_list = []
    for csv_path in tgt_dir_path.glob("*.csv"):
        csv_path_list.append(csv_path)
    csv_path_list.sort()
    tot_score = 0
    for csv_path in csv_path_list:
        min_score = None
        for line in open(csv_path):
            vals = line.replace("\n", "").split(",")
            score = float(vals[2])
            if min_score is None:
                min_score = score
            elif min_score > score:
                min_score = score
        tot_score += min_score
    return tot_score * 50

def main():
    while True:
        print(get_min_score())
        time.sleep(300)
if __name__ == "__main__":
    main()
import subprocess
from tqdm import tqdm
import time
def main():
    sum_score = 0.0
    norm = 0
    max_time = 0.0
    max_time_problem = None
    worst_score = 0
    worst_score_problem = None
    ini_cmd = "cargo build --release"
    print(subprocess.getoutput(ini_cmd))
    for d in range(5, 14 + 1):
        print("executing: d = ", d)
        sum_score0 = 0.0
        norm0 = 0
        max_time0 = 0
        tot_min = 60 * 3
        for i in tqdm(range(1, tot_min * 60 // 10 // 5)):
            cmd = "./target/release/ahc019 eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
            #cmd = "./pre_bin eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
            time0 = time.time()
            rets = subprocess.getoutput(cmd)
            time1 = time.time()
            try:
                score = int(rets.split("\n")[-1])
                max_time0 = max(max_time0, time1 - time0)
            except:
                print("conversion falied.")
                print("=========================")
                print(cmd)
                print("=========================")
                print(type(rets.split("\n")))
                print((rets.split("\n")))
                print(rets)
                print("=========================")
                return
            if worst_score < score:
                worst_score = score
                worst_score_problem = (d, i)
            if max_time < max_time0:
                max_time = max_time0
                max_time_problem = (d, i)
            sum_score0 += score
            norm0 += 1
        ave_score0 = sum_score0 / norm0
        print(ave_score0, worst_score_problem, max_time, max_time_problem)
        sum_score += sum_score0
        norm += norm0
    ave_score = sum_score / norm
    print(ave_score * 50, worst_score_problem, max_time, max_time_problem)

if __name__ == "__main__":
    main()

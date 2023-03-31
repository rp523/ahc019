import subprocess
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor
import time

tot_min = 20
def calc_score(d):
    sum_score = 0.0
    worst_score = 0
    worst_score_problem = None
    max_time = 0.0
    norm = 0
    for i in tqdm(range(1, 1 + tot_min * 60 // 5)):
        cmd = "./scan eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
        #cmd = "./pre_bin eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
        t0 = time.time()
        rets = subprocess.getoutput(cmd)
        t1 = time.time()
        t01 = t1 - t0
        try:
            score = float(rets.split("\n")[-1]) / 1000000000
            if max_time < t01:
                max_time = t01
        except:
            print("conversion falied.")
            print("=========================")
            print(cmd)
            print("=========================")
            print(type(rets.split("\n")))
            print((rets.split("\n")))
            print(int(rets.split("\n")[-1]))
            print(rets)
            print("=========================")
            return
        if worst_score < score:
            worst_score = score
            worst_score_problem = (d, i)
        sum_score += score
        norm += 1
    ave_score = sum_score / norm
    return ave_score, worst_score, worst_score_problem, max_time
def main():
    ini_cmd = "cargo build --release"
    print(subprocess.getoutput(ini_cmd))
    cp_cmd = "cp target/release/ahc019 scan"
    print(subprocess.getoutput(cp_cmd))
    THREAD = 10
    futures = []
    with ThreadPoolExecutor(max_workers = THREAD, thread_name_prefix = "thread") as pool:
        for d in range(5, 14 + 1):
            future = pool.submit(calc_score, d)
            futures.append(future)
    norm = 0
    sum_score = 0
    worst_score = 0
    max_time = 0.0
    worst_score_problem = None
    for (i, future) in enumerate(futures):
        d = i + 5
        ave_score0, worst_score0, worst_score_problem0, max_time0 = future.result()
        print("d={}".format(d), "ave:", ave_score0, "worst:", worst_score0, worst_score_problem0, "max_time", max_time0)
        if worst_score < worst_score0:
            worst_score = worst_score0
            worst_score_problem = worst_score_problem0
        if max_time < max_time0:
            max_time = max_time0
        sum_score += ave_score0
        norm += 1
    ave_score = sum_score / norm
    print(ave_score * 50, "worst:", worst_score, worst_score_problem, "max_time", max_time)

if __name__ == "__main__":
    main()

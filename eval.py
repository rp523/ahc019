import subprocess
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor

tot_min = 20
def calc(d):
    sum_score = 0.0
    worst_score = 0
    worst_score_problem = None
    norm = 0
    for i in tqdm(range(1, 1 + tot_min * 60 // 5)):
        cmd = "./scan eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
        #cmd = "./pre_bin eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
        rets = subprocess.getoutput(cmd)
        try:
            score = int(rets.split("\n")[-1])
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
    return ave_score, worst_score, worst_score_problem
def main():
    ini_cmd = "cargo build --release"
    print(subprocess.getoutput(ini_cmd))
    cp_cmd = "cp target/release/ahc019 scan"
    print(subprocess.getoutput(cp_cmd))
    THREAD = 10
    futures = []
    with ThreadPoolExecutor(max_workers = THREAD, thread_name_prefix = "thread") as pool:
        for d in range(5, 14 + 1):
            future = pool.submit(calc, d)
            futures.append(future)
    norm = 0
    sum_score = 0
    worst_score = 0
    worst_score_problem = None
    for (i, future) in enumerate(futures):
        d = i + 5
        ave_score0, worst_score0, worst_score_problem0 = future.result()
        print("d={}".format(d), "ave:", ave_score0, "worst:", worst_score0, "worst_at:", worst_score_problem0)
        if worst_score < worst_score0:
            worst_score_problem = worst_score_problem0
        sum_score += ave_score0
        norm += 1
    ave_score = sum_score / norm
    print(ave_score * 50, worst_score, worst_score_problem)

if __name__ == "__main__":
    main()

import subprocess
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor
import time
import optuna

tot_min = 20
def calc_score(
        d,
        anneal_a,
        anneal_b,
):
    sum_score = 0.0
    worst_score = 0
    worst_score_problem = None
    max_time = 0.0
    norm = 0
    for i in tqdm(range(1, 1 + tot_min * 60 // 5)):
        cmd = "./scan eval {} {} < tools/".format(anneal_a, anneal_b) + "in{}".format(d) + "/{0:04d}.txt".format(i)
        #cmd = "./pre_bin eval < tools/" + "in{}".format(d) + "/{0:04d}.txt".format(i)
        t0 = time.time()
        rets = subprocess.getoutput(cmd)
        t1 = time.time()
        t01 = t1 - t0
        try:
            score = int(rets.split("\n")[-1])
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
    with open("optuna{}.csv".format(d), "a") as f:
        f.write("{},{},{},{},{},{}\n".format(anneal_a, anneal_b, ave_score, worst_score, worst_score_problem, max_time))
    return ave_score

def gen_objective(d):
    def objective(trial):
        anneal_a = trial.suggest_uniform("anneal_a", 0.001, 10.0)
        anneal_b = trial.suggest_uniform("anneal_b", 0.0, 10.0)
        return calc_score(d, anneal_a, anneal_b)
    return objective
def optimize(d):
    study = optuna.create_study()
    optuna.logging.set_verbosity(optuna.logging.ERROR)
    study.optimize(gen_objective(d), n_trials=9999999999)    

def main():
    ini_cmd = "cargo build --release"
    print(subprocess.getoutput(ini_cmd))
    cp_cmd = "cp target/release/ahc019 scan"
    print(subprocess.getoutput(cp_cmd))
    THREAD = 10
    futures = []
    with ThreadPoolExecutor(max_workers = THREAD, thread_name_prefix = "thread") as pool:
        for d in range(5, 14 + 1):
            future = pool.submit(optimize, d)
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

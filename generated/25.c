int main25(int t,int v){
  int kipr, syw, ts, wbt, t6;

  kipr=t;
  syw=1;
  ts=2;
  wbt=0;
  t6=2;

  while (ts<=kipr-1) {
      wbt = wbt + syw;
      ts = ts + 1;
      t6 += 1;
      v += 2;
      t = t*t+wbt;
      wbt = wbt%6;
  }

}

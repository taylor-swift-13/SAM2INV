int main1(){
  int k66b, dqcn, ka6i, yv, v8s, uj;
  k66b=1-9;
  dqcn=k66b;
  ka6i=5;
  yv=0;
  v8s=dqcn;
  uj=k66b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ka6i >= 5;
  loop invariant uj >= k66b;
  loop invariant (v8s == -8) || (0 <= v8s && v8s < 7);
  loop invariant yv == (ka6i - 5) * (ka6i + 3);
  loop invariant -8 <= uj <= 6*ka6i - 38;
  loop invariant ka6i >= k66b;
  loop assigns yv, ka6i, uj, v8s;
*/
while (ka6i<=k66b) {
      yv = yv+2*ka6i-1;
      ka6i = ka6i + 1;
      uj = uj+(ka6i%7);
      v8s = v8s*v8s+v8s;
      v8s = v8s%7;
  }
}
int main1(int l){
  int me9, ke, t, kv, b8k, hlg;
  me9=(l%36)+10;
  ke=me9;
  t=25;
  kv=0;
  b8k=1;
  hlg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t + kv == 25;
  loop invariant (ke - me9) == (b8k - 1);
  loop invariant ke <= me9;
  loop invariant 0 <= t;
  loop assigns hlg, b8k, kv, ke, t;
*/
while (t>0&&ke<me9) {
      if (t<=b8k) {
          hlg = t;
      }
      else {
          hlg = b8k;
      }
      b8k = b8k + 1;
      kv = kv + hlg;
      ke++;
      t = t - hlg;
  }
}
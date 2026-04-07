int main1(int k){
  int o2, ks, gb, np;
  o2=k;
  ks=0;
  gb=o2;
  np=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ks >= 0 && (ks <= o2 || ks == 0);
  loop invariant o2 == \at(k, Pre);
  loop invariant 2 * np == k * ks * (ks - 1);
  loop invariant 6 * (gb - \at(k, Pre)) == k * ks * (ks - 1) * (ks + 1);
  loop assigns ks, np, gb;
*/
while (1) {
      if (!(ks<=o2-1)) {
          break;
      }
      np = np + ks*k;
      ks = ks + 1;
      gb = (np)+(gb);
  }
}
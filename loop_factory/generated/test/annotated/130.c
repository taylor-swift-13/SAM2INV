int main1(int t){
  int e, u, hj;
  e=t+14;
  u=e;
  hj=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(t, Pre) + 14;
  loop invariant u <= e;
  loop assigns hj, u, t;
*/
while (u<e) {
      hj = u%5;
      if (u>=hj) {
          hj = (u-hj)%5;
          hj = hj+hj-hj;
      }
      else {
          hj += hj;
      }
      u = u + 1;
      t += hj;
  }
}
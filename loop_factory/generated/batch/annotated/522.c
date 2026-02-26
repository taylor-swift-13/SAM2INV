int main1(int n,int p){
  int a, e, v;

  a=(p%12)+6;
  e=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == (p % 12) + 6;
  loop invariant v == 0 || v == p;
  loop invariant p == \at(p, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == p || v == 0;
  loop invariant a == (\at(p, Pre) % 12) + 6;
  loop invariant v == 0 || v == \at(p, Pre);
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v-v;
  }

}

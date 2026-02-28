int main1(int p,int q){
  int m, n, v;

  m=(q%37)+5;
  n=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == q || v == 0;
  loop invariant m == (q % 37) + 5;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m == (\at(q, Pre) % 37) + 5;
  loop invariant m == ((\at(q, Pre) % 37) + 5);
  loop invariant v == \at(q, Pre) || v == 0;
  loop invariant v == 0 || v == \at(q, Pre);
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v-v;
  }

}

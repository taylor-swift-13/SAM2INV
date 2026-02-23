int main1(int k,int q){
  int i, v, a, t, y, b;

  i=(k%15)+20;
  v=0;
  a=v;
  t=2;
  y=k;
  b=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 2 + v * y;
  loop invariant 0 <= v && v <= i;
  loop invariant y == \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == (\at(k, Pre) % 15) + 20;
  loop invariant v <= i;
  loop invariant y == k;
  loop invariant (0 <= v) && (v <= i);
  loop invariant i == (k % 15) + 20;
  loop assigns t, v;
*/
while (v<i) {
      t = t+y;
      v = v+1;
  }

}

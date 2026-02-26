int main1(int k,int q){
  int a, l, v, t;

  a=k+24;
  l=a;
  v=0;
  t=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t + v == a) || (t + v == a + 1);
  loop invariant l == a;
  loop invariant a == \at(k, Pre) + 24;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v >= 0;
  loop invariant a == k + 24;
  loop invariant (v == 0) ==> (t == a);
  loop invariant (v > 0) ==> (t == a - v + 1);
  loop invariant t <= a;
  loop invariant a - v <= t;

  loop assigns t, v;
*/
while (l-3>=0) {
      t = a-v;
      v = v+1;
  }

}

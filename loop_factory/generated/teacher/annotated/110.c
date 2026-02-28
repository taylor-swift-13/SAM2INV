int main1(int m){
  int l, t, v, a;

  l=57;
  t=l;
  v=5;
  a=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 57;
  loop invariant m == \at(m, Pre);
  loop invariant t >= 0;
  loop invariant t <= 57;
  loop invariant t <= l;
  loop assigns t;
*/
while (t>0) {
      t = t-1;
  }

}

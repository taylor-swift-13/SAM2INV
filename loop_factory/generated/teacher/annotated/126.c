int main1(int k){
  int d, p, e, v;

  d=k;
  p=0;
  e=8;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == p + 8;
  loop invariant d == k;

  loop invariant k == \at(k, Pre);
  loop invariant e - p == 8;
  loop invariant 0 <= p;
  loop invariant p >= 0;
  loop invariant 0 <= p && (d >= 0 ==> p <= d);
  loop invariant d == \at(k, Pre);
  loop invariant e == 8 + p;
  loop assigns e, p;
*/
while (p<=d-1) {
      e = e+1;
      p = p+1;
  }

}

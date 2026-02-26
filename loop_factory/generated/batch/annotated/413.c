int main1(int a,int q){
  int r, i, v, e;

  r=a;
  i=r;
  v=0;
  e=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == a;
  loop invariant i == a;
  loop invariant v >= 0;
  loop invariant e + v <= a + 1;

  loop invariant e <= r;
  loop invariant e >= r - v;
  loop invariant e <= a;
  loop invariant (v == 0 ==> e == a);
  loop invariant (v > 0 ==> e == a - (v - 1));
  loop invariant i == r;
  loop invariant e >= a - v;
  loop assigns e, v;
*/
while (i-1>=0) {
      e = r-v;
      v = v+1;
  }

}

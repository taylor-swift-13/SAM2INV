int main1(int a,int m){
  int r, e, v, l;

  r=51;
  e=r;
  v=r;
  l=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + 6*l == 357;
  loop invariant e == r;
  loop invariant v >= e;
  loop invariant l <= r;
  loop invariant e >= 0;
  loop invariant e == 51;
  loop invariant v == 357 - 6*l;
  loop invariant l <= 51;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == 51;
  loop invariant v >= 51;
  loop assigns v, l;
*/
while (e>0) {
      v = v+4;
      v = v+1;
      l = l-1;
      v = v+1;
  }

}

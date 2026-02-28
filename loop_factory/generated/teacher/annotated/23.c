int main1(int a,int b){
  int r, f, v, p;

  r=64;
  f=0;
  v=b;
  p=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(b, Pre) + 2*p*f;
  loop invariant p == r;
  loop invariant f <= r;
  loop invariant f >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant 0 <= f;
  loop invariant a == \at(a, Pre);
  loop invariant v == b + f*(p+p);
  loop invariant r == 64;
  loop invariant v == b + 2*p*f;
  loop assigns v, f;
*/
while (f<r) {
      v = v+p+p;
      f = f+1;
  }

}

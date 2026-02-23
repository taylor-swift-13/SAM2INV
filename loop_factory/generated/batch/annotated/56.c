int main1(int m,int n){
  int b, f, v, x;

  b=62;
  f=0;
  v=b;
  x=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 0;
  loop invariant f <= b;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant f >= 0;
  loop invariant 0 <= f;
  loop assigns x, f;
*/
while (f<b) {
      x = x+x;
      f = f+1;
  }

}

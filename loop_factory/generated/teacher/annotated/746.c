int main1(int a,int b,int k,int n){
  int p, s, x, v, j;

  p=73;
  s=2;
  x=s;
  v=0;
  j=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == (x*x + x - 6)/2;
  loop invariant x % 2 == 0;
  loop invariant x >= 2;

  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 2*v == x*x + x - 6;
  loop invariant 24*(j - 73) == 2*x*x*x + 3*x*x - 38*x + 48;
  loop invariant j >= 73;
  loop invariant p == 73;
  loop invariant v >= 0;

  loop assigns x, v, j;
*/
while (1) {
      x = x+1;
      v = v+x;
      j = j+v;
      x = x+1;
      v = v+x;
  }

}

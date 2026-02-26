int main1(int b,int p){
  int f, n, v, c;

  f=p;
  n=3;
  v=b;
  c=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(p, Pre);
  loop invariant c == 3*n - 10;
  loop invariant 2*(v - \at(b, Pre)) == n*n + 9*n - 36;
  loop invariant n >= 3;
  loop invariant 2*v == 2*\at(b,Pre) + n*n + 9*n - 36;
  loop invariant b == \at(b,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant v == b + 8*(n - 3) + ((n - 3)*(n - 4))/2;
  loop invariant f == p;

  loop assigns v, n, c;
*/
while (1) {
      if (n>=f) {
          break;
      }
      v = v+2;
      n = n+1;
      v = v+2;
      c = c+3;
      v = v+n;
  }

}

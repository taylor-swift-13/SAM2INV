int main1(int a,int b,int k,int n){
  int y, u, v, m, x;

  y=n+25;
  u=0;
  v=k;
  m=2;
  x=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant (x == b || x == -b) && (m == 2 || m == 2 + b) && ((x == b) ==> (m == 2)) && ((x == -b) ==> (m == 2 + b));
  loop invariant y == n + 25;

  loop invariant (v == y) || (((v - k) % 3) == 0);
  loop invariant x*x == b*b;

  loop invariant (m == 2) || (m == 2 + b);
  loop invariant (x == b) || (x == -b);
  loop invariant a == \at(a, Pre);
  loop invariant v <= y || v == k;
  loop invariant m == 2 || m == 2 + b;
  loop invariant x == b || x == -b;
  loop invariant (v == y) || ((v - k) % 3 == 0);
  loop assigns v, m, x;
*/
while (1) {
      if (v+3<=y) {
          v = v+3;
      }
      else {
          v = y;
      }
      m = m+x;
      x = x+v;
      x = v-x;
  }

}

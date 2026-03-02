int main1(int m,int n){
  int o, x, d, c;

  o=n+25;
  x=0;
  d=o;
  c=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == n + 25;
  loop invariant x >= 0;




  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant o == \at(n, Pre) + 25;
  loop invariant c == 2*d - o;
  loop invariant x >= 0 &&
                   o == \at(n, Pre) + 25 &&
                   n == \at(n, Pre) &&
                   m == \at(m, Pre);
  loop invariant o == \at(n,Pre) + 25;
  loop invariant n == \at(n,Pre);
  loop invariant m == \at(m,Pre);
  loop assigns d, c, x;
*/
while (1) {
      d = d*2;
      c = c+d;
      x = x+1;
  }

}

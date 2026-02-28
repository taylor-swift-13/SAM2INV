int main1(int m,int n){
  int w, t, d;

  w=79;
  t=0;
  d=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant w == 79;
  loop invariant t % 2 == 0;
  loop invariant t <= w - 1;
  loop invariant (t == 0) ==> (d == 79);
  loop invariant t <= w;
  loop invariant 0 <= t;
  loop invariant 0 <= t <= w;
  loop invariant (t == 0) ==> (d == w);
  loop assigns d, t;
*/
while (t<=w-2) {
      d = d-d;
      if ((t%2)==0) {
          d = d+1;
      }
      t = t+2;
  }

}

int main1(int a,int b,int m,int p){
  int r, d, c, v;

  r=b-5;
  d=r;
  c=0;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(b, Pre) - 5;
  loop invariant d == r;
  loop invariant v == -3;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant r == b - 5;
  loop invariant (d < r/2) ==> (c <= 0);
  loop invariant (d >= r/2) ==> (c >= 0);
  loop invariant (r >= 0) ==> (c % 3 == 0);
  loop invariant c >= 0;
  loop invariant c % 3 == 0;
  loop assigns c;
*/
while (d>2) {
      if (d<r/2) {
          c = c+v;
      }
      else {
          c = c+1;
      }
      c = c+2;
  }

}

int main1(int b,int p){
  int d, u, v, k;

  d=p+5;
  u=0;
  v=0;
  k=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == p + 5 && 0 <= v;
  loop invariant k % 2 == 1 && k >= 1;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant v >= 0 && k % 2 == 1;
  loop invariant d == p + 5;

  loop invariant k >= 1;
  loop invariant (v < d/2) ==> k == 1;

  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v < d/2 ==> k == 1;

  loop invariant 0 <= v;

  loop invariant (v < d/2) ==> (k == 1);


  loop invariant v >= 0;
  loop invariant (v <= d/2) ==> (k == 1);

  loop invariant p == \at(p, Pre) && d == p + 5;
  loop invariant v >= 0 && k >= 1 && k % 2 == 1 && b == \at(b, Pre);
  loop assigns k, v;
*/
while (v<d) {
      if (v>=d/2) {
          k = k+2;
      }
      v = v+1;
  }

}

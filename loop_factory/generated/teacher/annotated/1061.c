int main1(int m,int p){
  int q, s, b;

  q=p;
  s=q;
  b=s;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == \at(p, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant s <= \at(p, Pre);
  loop invariant (s == \at(p, Pre)) ==> (b == \at(p, Pre));
  loop invariant q == \at(p,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant s <= \at(p,Pre);
  loop invariant (s == \at(p,Pre) ==> b == \at(p,Pre));
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant \at(p, Pre) >= 0 ==> 0 <= s && s <= \at(p, Pre);
  loop invariant s >= 1 ==> b >= 0;
  loop invariant q == \at(p, Pre) && p == \at(p, Pre) && m == \at(m, Pre);
  loop invariant s <= \at(p, Pre) && b >= \at(p, Pre);
  loop invariant b >= s;
  loop invariant q == \at(p,Pre) && m == \at(m,Pre);
  loop invariant (\at(p,Pre) >= 0) ==> (0 <= s && s <= \at(p,Pre));
  loop invariant q == \at(p, Pre) && s <= \at(p, Pre) && (\at(p, Pre) >= 0 ==> s >= 0);
  loop invariant p == \at(p, Pre) && m == \at(m, Pre);
  loop invariant s <= q;
  loop invariant b == \at(p, Pre) || b >= 0;

  loop assigns b, s;
*/
while (s>=1) {
      b = b*b;
      b = b*b+b;
      s = s/2;
  }

}

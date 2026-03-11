int main1(int l,int k){
  int hx, q1v, by, p, ubk, fa;
  hx=80;
  q1v=0;
  by=0;
  p=0;
  ubk=l;
  fa=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p;
  loop invariant p <= hx;
  loop invariant by == p * \at(l, Pre);
  loop invariant ubk == \at(l, Pre) + p * hx;
  loop invariant 0 <= fa;
  loop invariant fa <= 3 * p;
  loop invariant q1v == 0;
  loop invariant hx == 80;
  loop invariant l == \at(l, Pre);
  loop invariant ((p % 4) == 0 && fa == (p / 4) * 6)
                   || ((p % 4) == 1 && fa == (p / 4) * 6 + 1)
                   || ((p % 4) == 2 && fa == (p / 4) * 6 + 3)
                   || ((p % 4) == 3 && fa == (p / 4) * 6 + 6);
  loop assigns by, p, ubk, fa;
*/
while (p<hx) {
      by += l;
      p++;
      ubk = ubk+hx-q1v;
      fa = fa+(p%4);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ubk == \at(l, Pre) + hx * hx;
  loop invariant by >= (hx * \at(l, Pre));
  loop invariant hx == 80;
  loop invariant k == \at(k, Pre);
  loop assigns by, fa, l;
*/
while (by<ubk) {
      by = by + 1;
      fa += l;
      l = l + by;
      l = l*2;
  }
}
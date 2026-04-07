int main1(int r){
  int nj2, ma, p2i, x65o;
  nj2=r+21;
  ma=0;
  p2i=1;
  x65o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((ma == 0 && p2i == 1 && x65o == 0)
                    || (ma == nj2 && p2i == r && x65o == 2));
  loop invariant nj2 == \at(r, Pre) + 21;
  loop invariant r == \at(r, Pre);
  loop invariant (ma == 0 && p2i == 1 && x65o == 0) || (ma == nj2 && p2i == r && x65o == 2);
  loop invariant ((ma == 0) && (p2i == 1) && (x65o == 0)) ||
                   ((ma == nj2) && (p2i == r) && (x65o == 2));
  loop invariant (ma == 0 ==> (p2i == 1 && x65o == 0));
  loop assigns p2i, x65o, ma;
*/
while (ma < nj2) {
      p2i = p2i * r;
      x65o += 2;
      ma = nj2;
  }
}
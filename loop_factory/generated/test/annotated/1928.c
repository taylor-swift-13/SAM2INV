int main1(int l){
  int lb, gx9h, iuoz;
  lb=0;
  gx9h=l;
  iuoz=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iuoz == 1;
  loop invariant (gx9h - lb) == \at(l, Pre);
  loop invariant (l == 0) || (l == \at(l, Pre));
  loop invariant 0 <= lb;
  loop invariant lb <= 1;
  loop invariant (lb == 0) <==> (l == \at(l, Pre));
  loop assigns lb, gx9h, l;
*/
while (1) {
      if (!(l > 0)) {
          break;
      }
      lb = lb + iuoz;
      gx9h = gx9h + iuoz;
      l = 0;
  }
}
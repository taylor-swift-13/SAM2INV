int main1(int u,int d){
  int am, mh, cj;
  am=18;
  mh=0;
  cj=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == \at(u, Pre) + mh*(mh - 1)/2;
  loop invariant (0 <= mh && mh <= am);
  loop invariant am == 18;
  loop assigns cj, u, mh;
*/
while (1) {
      if (!(mh<am)) {
          break;
      }
      cj = cj+u+d;
      cj++;
      u = u + mh;
      mh = mh + 1;
  }
}
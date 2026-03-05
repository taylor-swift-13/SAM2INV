int main1(int m){
  int u, fl, msi;
  u=m;
  fl=u;
  msi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant msi == 0;
  loop invariant fl <= u;
  loop invariant m - \at(m, Pre) == msi * (fl - \at(m, Pre));
  loop invariant \at(m, Pre) <= fl;
  loop invariant u == \at(m, Pre);
  loop invariant fl >= \at(m, Pre);
  loop assigns m, msi, fl;
*/
while (fl<u) {
      if (fl%2==0) {
          if (msi>0) {
              msi = msi - 1;
              msi += 1;
          }
      }
      else {
          if (msi>0) {
              msi = msi - 1;
              msi += 1;
          }
      }
      fl = fl + 1;
      m = m + msi;
  }
}
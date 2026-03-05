int main1(int e,int l){
  int yl, f5e, u9x0;
  yl=(e%38)+14;
  f5e=1;
  u9x0=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yl == (\at(e,Pre) % 38) + 14;
  loop invariant e >= \at(e,Pre);
  loop invariant (l - \at(l,Pre)) == 3*((e - \at(e,Pre))/2) + 2*((e - \at(e,Pre)) % 2);
  loop invariant u9x0 == 1 + ((e - \at(e,Pre)) % 2);
  loop invariant f5e == 1;
  loop assigns l, e, u9x0;
*/
while (f5e<=yl-2) {
      if (u9x0==1) {
          u9x0 = 2;
      }
      else {
          if (u9x0==2) {
              u9x0 = 1;
          }
      }
      l += u9x0;
      e += 1;
  }
}
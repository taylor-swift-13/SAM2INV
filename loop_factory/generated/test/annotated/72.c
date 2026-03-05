int main1(int o,int z){
  int d6, m2v, mls;
  d6=z-10;
  m2v=4;
  mls=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mls % 2 == 0;
  loop invariant mls >= 0;
  loop invariant o == \at(o, Pre) + (mls/2)*m2v;
  loop invariant m2v == 4;
  loop invariant d6 == z - 10;
  loop invariant z == \at(z, Pre);
  loop invariant d6 >= 0 ==> mls <= d6 + 1;
  loop assigns mls, o;
*/
while (mls<d6) {
      mls += 2;
      if (mls<=mls) {
          mls = mls;
      }
      o = o + m2v;
  }
}
int main1(int t){
  int oz, gxn, jc7z, u;
  oz=55;
  gxn=0;
  jc7z=0;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((gxn == 0 && jc7z == 0) || (gxn >= 1 && jc7z == 1));
  loop invariant gxn <= oz;
  loop invariant u == 0;
  loop invariant t == \at(t, Pre);
  loop invariant oz == 55;
  loop invariant jc7z == 0 || jc7z == 1;
  loop invariant 0 <= gxn;
  loop assigns gxn, jc7z, u;
*/
while (jc7z>0&&gxn<oz) {
      if (jc7z<jc7z) {
          jc7z = jc7z;
      }
      else {
          jc7z = jc7z;
      }
      jc7z -= jc7z;
      u += jc7z;
      jc7z++;
      gxn = gxn + 1;
  }
}
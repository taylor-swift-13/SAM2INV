int main1(int w,int f){
  int ywm, t5p, ik, x5z;
  ywm=8;
  t5p=3;
  ik=7;
  x5z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t5p <= ywm;
  loop invariant t5p >= 3;
  loop invariant ik >= 0;
  loop invariant f == \at(f, Pre) + ywm * (t5p - 3);
  loop invariant 0 <= x5z;
  loop invariant x5z <= 4;
  loop invariant ywm == 8;
  loop invariant w == \at(w, Pre);
  loop assigns f, ik, t5p, x5z;
*/
while (t5p<ywm) {
      x5z = t5p%5;
      if (t5p>=ik) {
          ik = (t5p-ik)%5;
          ik = ik+x5z-ik;
      }
      else {
          ik = ik + x5z;
      }
      t5p += 1;
      f = f + ywm;
  }
}
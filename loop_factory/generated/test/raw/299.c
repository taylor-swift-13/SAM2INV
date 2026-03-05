int main1(int w,int f){
  int ywm, t5p, ik, x5z;

  ywm=8;
  t5p=3;
  ik=7;
  x5z=0;

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

int main1(){
  int ib, hwq, i3, jz, a, vs, ro;

  ib=32;
  hwq=0;
  i3=0;
  jz=ib;
  a=0;
  vs=-2;
  ro=hwq;

  while (1) {
      if (!(i3<ib)) {
          break;
      }
      i3 += 8;
      if (i3%1==0) {
          i3 = i3 + 1;
      }
      vs += 2;
      a++;
      jz += hwq;
      ro += 2;
  }

}

int main1(){
  int t, g6v, i0, ck, q5i, okx8;

  t=(1%12)+18;
  g6v=0;
  i0=g6v;
  ck=0;
  q5i=t;
  okx8=(1%35)+8;

  while (1) {
      if (!(okx8>0)) {
          break;
      }
      i0 = (ck*ck)+(i0);
      q5i = q5i+okx8*okx8;
      ck = ck+okx8*okx8;
      i0 = i0*2;
      okx8 -= 1;
  }

}

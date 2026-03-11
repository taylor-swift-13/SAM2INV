int main1(){
  int sxl8, vf1, nf2, al4, s1, c4;

  sxl8=60;
  vf1=sxl8+3;
  nf2=0;
  al4=0;
  s1=sxl8;
  c4=0;

  while (al4<=sxl8-1) {
      al4 += 1;
      nf2++;
      s1 += nf2;
      s1 = s1 + c4;
  }

  while (1) {
      nf2 = nf2 + vf1;
      vf1 = vf1 + c4;
      c4++;
      if (c4>=al4) {
          break;
      }
  }

}

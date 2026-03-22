int main1(){
  int ik, c5, jdr, p, oo;

  ik=0;
  c5=(1%28)+8;
  jdr=(1%22)+5;
  p=0;
  oo=ik;

  while (jdr!=0) {
      if (jdr%2==1) {
          p += c5;
          jdr = jdr - 1;
      }
      c5 = 2*c5;
      jdr = jdr/2;
      oo += jdr;
      oo = oo%6;
  }

}

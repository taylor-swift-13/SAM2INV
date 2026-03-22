int main1(){
  int t, b6s, om, u4, pc;

  t=1;
  b6s=2;
  om=0;
  u4=b6s;
  pc=t;

  while (om<=t-1) {
      om += 2;
      if (om<=pc) {
          pc = om;
      }
      u4 = u4+om-pc;
  }

}

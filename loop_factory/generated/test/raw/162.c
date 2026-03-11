int main1(int t,int z){
  int dwk8, em, s, aw, m5v;

  dwk8=(z%35)+6;
  em=dwk8;
  s=22;
  aw=1;
  m5v=0;

  while (1) {
      if (!(s>0&&aw<=dwk8)) {
          break;
      }
      if (s>aw) {
          s -= aw;
      }
      else {
          s = 0;
      }
      m5v++;
      em = em + 1;
      aw = aw + 1;
  }

}

int main1(int p){
  int lu, nl4, pc, unr, m26a;

  lu=p-6;
  nl4=0;
  pc=0;
  unr=0;
  m26a=5;

  while (pc<lu&&m26a>0) {
      pc++;
      unr += m26a;
      p += nl4;
      m26a -= 1;
  }

}

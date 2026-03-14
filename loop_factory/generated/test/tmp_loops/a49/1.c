int main1(int o){
  int dq, m9, p;

  dq=108;
  m9=0;
  p=0;

  while (p<dq) {
      p++;
      m9 = m9 + o;
      o += m9;
  }

  while (dq<p) {
      dq = dq + 1;
      m9 = m9 + o;
      o += p;
  }

}

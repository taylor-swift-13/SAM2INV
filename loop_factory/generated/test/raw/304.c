int main1(int d){
  int ul, t1, n5, a, s2;

  ul=d-8;
  t1=0;
  n5=0;
  a=2;
  s2=0;

  while (n5<ul) {
      a = a + n5;
      n5++;
      s2 = s2 + n5;
  }

  while (1) {
      a++;
      d = d + a;
      t1 = t1 + 1;
      if (t1>=ul) {
          break;
      }
  }

}

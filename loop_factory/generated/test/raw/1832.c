int main1(){
  int s2a, fn1, ds4, lt, q;

  s2a=1;
  fn1=2;
  ds4=0;
  lt=0;
  q=fn1;

  while (1) {
      if (!(lt<s2a)) {
          break;
      }
      ds4 = ds4 + 1;
      lt += 1;
      q = q + ds4;
      q = q*4+3;
  }

}

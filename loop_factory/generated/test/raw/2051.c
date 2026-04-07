int main1(){
  int t7, ktt, v6, a, c;

  t7=1;
  ktt=0;
  v6=t7;
  a=0;
  c=0;

  while (1) {
      if (!(ktt < t7)) {
          break;
      }
      a += v6;
      ktt = ktt + 1;
      c = c + a;
      v6 = v6+t7-ktt;
  }

}

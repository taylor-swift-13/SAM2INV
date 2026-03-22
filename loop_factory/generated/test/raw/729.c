int main1(){
  int kp, n, pl;

  kp=0;
  n=(1%28)+10;
  pl=13;

  while (n>kp) {
      n = n - kp;
      kp = kp + 1;
      pl += n;
  }

}

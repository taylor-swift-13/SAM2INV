int main1(){
  int l, n, s, wo;

  l=13;
  n=l;
  s=3;
  wo=1;

  while (n<l) {
      if (s>=12) {
          wo = -1;
      }
      if (s<=3) {
          wo = 1;
      }
      s += wo;
      n += 1;
  }

}

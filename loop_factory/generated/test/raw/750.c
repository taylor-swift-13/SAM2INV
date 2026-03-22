int main1(){
  int kp, ib, g3p, meg;

  kp=(1%60)+60;
  ib=(1%9)+2;
  g3p=0;
  meg=0;

  while (1) {
      if (kp<=ib*g3p+meg) {
          break;
      }
      if (meg==ib-1) {
          meg = 0;
          g3p += 1;
      }
      else {
          meg++;
      }
      kp = kp + meg;
  }

}
